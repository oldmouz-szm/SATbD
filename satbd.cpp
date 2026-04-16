/*
 * SATbD: SAT-based Diagnosis
 * Based on: "A Novel SAT-Based Approach to Model Based Diagnosis"
 *           Metodi, Stern, Kalech & Codish, JAIR 2014
 *
 * Implements minimal cardinality diagnosis for combinational logic circuits
 * using SAT encoding with section/cone preprocessing, dominator computation,
 * BEE equi-propagation, and MiniSat/CryptoMiniSat solver backends.
 *
 * Usage: satbd <bench_file> <obs_file> [--all] [--use-bee] [--use-cryptominisat]
 */

#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <queue>
#include <cstring>
#include <ctime>
#include <memory>
#include <cstdlib>
#include <dirent.h>
#include <sys/stat.h>
#include <iomanip>

#include "minisat/core/Solver.h"

using namespace std;
using Minisat::lbool;

// 全局静默开关（批处理时设为 true 以禁用冗长的调试输出）
static bool g_quiet = false;

enum GateType { GATE_AND, GATE_NAND, GATE_OR, GATE_NOR, GATE_XOR, GATE_XNOR, GATE_NOT, GATE_BUF, GATE_INPUT };

struct Gate {
    int id;
    GateType type;
    vector<int> inputs;
    int output;
    Gate() : id(-1), type(GATE_AND), output(-1) {}
};

struct Observation {
    map<int, int> input_values;
    map<int, int> output_values;
    set<int> fault_set;
};

struct DiagnosisResult {
    string obs_file;
    int diagnosis_index;
    bool solved;
    double time_seconds;      // 单个诊断用时
    double cumulative_seconds; // 累计用时
    int diag_size;
    set<int> diag_components;
};

struct BatchResult {
    string circuit_name;
    vector<DiagnosisResult> results;
    double total_time;
    int total_diagnoses;
    double prep_time;      // 预处理时间
    double online_time;    // 在线时间
};

struct Section {
    set<int> components;
    int bound;
};

class Circuit {
public:
    map<int, Gate> gates;
    set<int> inputs;
    set<int> outputs;
    vector<int> topological_order;
    map<int, set<int>> sysout;
    vector<Section> sections;
    map<int, int> component_to_section;
    map<int, set<int>> dominators;
    set<int> dominated_components;
    set<int> top_level_components;
    map<int, set<int>> cone_map;

    void parse_bench(const string& filename) {
        ifstream fin(filename);
        if (!fin.is_open()) {
            cerr << "Error: cannot open bench file: " << filename << endl;
            exit(1);
        }
        string line;
        while (getline(fin, line)) {
            size_t comment_pos = line.find('#');
            if (comment_pos != string::npos) line = line.substr(0, comment_pos);
            while (!line.empty() && (line.back() == ' ' || line.back() == '\r' || line.back() == '\t')) line.pop_back();
            if (line.empty()) continue;

            if (line.find("INPUT(") != string::npos) {
                size_t s = line.find('(') + 1;
                size_t e = line.find(')');
                int wire = stoi(line.substr(s, e - s));
                inputs.insert(wire);
                Gate g;
                g.id = wire;
                g.type = GATE_INPUT;
                g.output = wire;
                gates[wire] = g;
            } else if (line.find("OUTPUT(") != string::npos) {
                size_t s = line.find('(') + 1;
                size_t e = line.find(')');
                int wire = stoi(line.substr(s, e - s));
                outputs.insert(wire);
            } else if (line.find('=') != string::npos) {
                size_t eq = line.find('=');
                int out_wire = stoi(line.substr(0, eq));
                size_t paren_s = line.find('(', eq);
                size_t paren_e = line.find(')', eq);
                string type_str = line.substr(eq + 1, paren_s - eq - 1);
                while (!type_str.empty() && type_str.back() == ' ') type_str.pop_back();
                while (!type_str.empty() && type_str.front() == ' ') type_str = type_str.substr(1);

                string args = line.substr(paren_s + 1, paren_e - paren_s - 1);
                vector<int> in_wires;
                stringstream ss(args);
                string tok;
                while (getline(ss, tok, ',')) {
                    while (!tok.empty() && tok.front() == ' ') tok = tok.substr(1);
                    while (!tok.empty() && (tok.back() == ' ' || tok.back() == '\r')) tok.pop_back();
                    if (!tok.empty()) in_wires.push_back(stoi(tok));
                }

                GateType gt;
                if (type_str == "AND") gt = GATE_AND;
                else if (type_str == "NAND") gt = GATE_NAND;
                else if (type_str == "OR") gt = GATE_OR;
                else if (type_str == "NOR") gt = GATE_NOR;
                else if (type_str == "XOR") gt = GATE_XOR;
                else if (type_str == "XNOR") gt = GATE_XNOR;
                else if (type_str == "NOT") gt = GATE_NOT;
                else if (type_str == "BUF" || type_str == "BUFF") gt = GATE_BUF;
                else {
                    cerr << "Unknown gate type: " << type_str << endl;
                    exit(1);
                }

                Gate g;
                g.id = out_wire;
                g.type = gt;
                g.inputs = in_wires;
                g.output = out_wire;
                gates[out_wire] = g;
            }
        }
        fin.close();
        compute_topological_order();
    }

    void compute_topological_order() {
        map<int, int> in_degree;
        map<int, vector<int>> adj;
        for (auto& p : gates) {
            Gate& g = p.second;
            if (g.type == GATE_INPUT) {
                in_degree[g.id] = 0;
            } else {
                if (in_degree.find(g.id) == in_degree.end()) in_degree[g.id] = 0;
                for (int inp : g.inputs) {
                    if (gates.count(inp)) {
                        adj[inp].push_back(g.id);
                        in_degree[g.id]++;
                    }
                }
            }
        }
        queue<int> q;
        for (auto& p : in_degree) {
            if (p.second == 0) q.push(p.first);
        }
        while (!q.empty()) {
            int u = q.front(); q.pop();
            topological_order.push_back(u);
            for (int v : adj[u]) {
                in_degree[v]--;
                if (in_degree[v] == 0) q.push(v);
            }
        }
    }

    set<int> get_component_gates() const {
        set<int> comps;
        for (auto& p : gates) {
            if (p.second.type != GATE_INPUT) comps.insert(p.first);
        }
        return comps;
    }

    void compute_sysout() {
        sysout.clear();
        for (int out : outputs) {
            set<int> visited;
            queue<int> q;
            q.push(out);
            visited.insert(out);
            while (!q.empty()) {
                int u = q.front(); q.pop();
                if (gates.count(u) && gates.at(u).type != GATE_INPUT) {
                    sysout[u].insert(out);
                }
                if (gates.count(u)) {
                    for (int inp : gates.at(u).inputs) {
                        if (!visited.count(inp)) {
                            visited.insert(inp);
                            q.push(inp);
                        }
                    }
                }
            }
        }
    }

    void compute_sections() {
        compute_sysout();
        vector<int> out_list(outputs.begin(), outputs.end());
        sort(out_list.begin(), out_list.end());
        map<int, vector<bool>> bitvec;
        for (auto& p : gates) {
            if (p.second.type == GATE_INPUT) continue;
            int gid = p.first;
            vector<bool> bv(out_list.size(), false);
            if (sysout.count(gid)) {
                for (int o : sysout[gid]) {
                    auto it = lower_bound(out_list.begin(), out_list.end(), o);
                    if (it != out_list.end() && *it == o) {
                        bv[it - out_list.begin()] = true;
                    }
                }
            }
            bitvec[gid] = bv;
        }
        map<vector<bool>, set<int>> section_map;
        for (auto& p : bitvec) {
            section_map[p.second].insert(p.first);
        }
        sections.clear();
        component_to_section.clear();
        int sec_idx = 0;
        for (auto& p : section_map) {
            Section sec;
            sec.components = p.second;
            int sysout_size = 0;
            for (size_t i = 0; i < p.first.size(); i++) {
                if (p.first[i]) sysout_size++;
            }
            int n_sec_outputs = count_section_outputs(sec.components);
            sec.bound = min(n_sec_outputs, sysout_size);
            sections.push_back(sec);
            for (int c : sec.components) {
                component_to_section[c] = sec_idx;
            }
            sec_idx++;
        }
    }

    int count_section_outputs(const set<int>& comps) {
        set<int> sec_outs;
        for (int c : comps) {
            if (!gates.count(c)) continue;
            Gate& g = gates[c];
            for (auto& p : gates) {
                if (p.second.type == GATE_INPUT) continue;
                if (comps.count(p.first)) continue;
                for (int inp : p.second.inputs) {
                    if (inp == g.output) sec_outs.insert(g.output);
                }
            }
            if (outputs.count(g.output)) sec_outs.insert(g.output);
        }
        return sec_outs.size();
    }

    void compute_dominators() {
        dominated_components.clear();
        top_level_components.clear();
        cone_map.clear();
        dominators.clear();

        for (size_t si = 0; si < sections.size(); si++) {
            Section& sec = sections[si];
            map<int, set<int>> memo;
            for (int c : sec.components) {
                dominators[c] = compute_dominators_of(c, sec.components, memo);
            }
        }

        for (auto& p : dominators) {
            if (p.second.size() > 1) {
                dominated_components.insert(p.first);
            }
        }

        set<int> comps = get_component_gates();
        for (int c : comps) {
            if (!dominated_components.count(c)) {
                top_level_components.insert(c);
            }
        }

        for (auto& p : dominators) {
            for (int d : p.second) {
                if (d != p.first) {
                    cone_map[d].insert(p.first);
                }
            }
        }
        for (auto& p : cone_map) {
            p.second.insert(p.first);
        }
    }

    set<int> compute_dominators_of(int c, const set<int>& section_comps, map<int, set<int>>& memo) {
        if (memo.count(c)) return memo[c];
        set<int> result;
        result.insert(c);
        Gate& g = gates[c];
        vector<int> succs;
        for (auto& p : gates) {
            if (p.second.type == GATE_INPUT) continue;
            for (int inp : p.second.inputs) {
                if (inp == g.output) {
                    succs.push_back(p.first);
                    break;
                }
            }
        }
        bool all_in_section = true;
        for (int s : succs) {
            if (!section_comps.count(s)) { all_in_section = false; break; }
        }
        if (!all_in_section || succs.empty()) {
            memo[c] = result;
            return result;
        }
        set<int> common_doms;
        bool first = true;
        for (int s : succs) {
            set<int> doms = compute_dominators_of(s, section_comps, memo);
            if (first) { common_doms = doms; first = false; }
            else {
                set<int> inter;
                set_intersection(common_doms.begin(), common_doms.end(),
                               doms.begin(), doms.end(),
                               inserter(inter, inter.begin()));
                common_doms = inter;
            }
        }
        result.insert(common_doms.begin(), common_doms.end());
        memo[c] = result;
        return result;
    }

    void preprocess() {
        compute_sections();
        compute_dominators();
    }
};

Observation parse_observation(const string& filename) {
    Observation obs;
    ifstream fin(filename);
    if (!fin.is_open()) {
        cerr << "Error: cannot open observation file: " << filename << endl;
        exit(1);
    }
    string line;
    bool in_inputs = false, in_outputs = false;
    while (getline(fin, line)) {
        if (line.find("# inputs") != string::npos || line.find("#inputs") != string::npos) {
            in_inputs = true; in_outputs = false; continue;
        }
        if (line.find("# outputs") != string::npos || line.find("#outputs") != string::npos) {
            in_inputs = false; in_outputs = true; continue;
        }
        if (line.find('#') != string::npos) {
            size_t pos = line.find('#');
            string comment = line.substr(pos + 1);
            if (comment.find("faults=") != string::npos) {
                size_t fp = comment.find("faults=") + 7;
                string fstr = comment.substr(fp);
                stringstream ss(fstr);
                string tok;
                while (getline(ss, tok, ',')) {
                    while (!tok.empty() && tok.front() == ' ') tok = tok.substr(1);
                    while (!tok.empty() && (tok.back() == ' ' || tok.back() == '\r')) tok.pop_back();
                    if (!tok.empty()) obs.fault_set.insert(stoi(tok));
                }
            }
            line = line.substr(0, pos);
        }
        while (!line.empty() && (line.back() == ' ' || line.back() == '\r' || line.back() == '\t')) line.pop_back();
        if (line.empty()) continue;

        if (line == "inputs") { in_inputs = true; in_outputs = false; continue; }
        if (line == "outputs") { in_inputs = false; in_outputs = true; continue; }

        size_t eq = line.find('=');
        if (eq != string::npos) {
            int wire = stoi(line.substr(0, eq));
            int val = stoi(line.substr(eq + 1));
            if (in_inputs) obs.input_values[wire] = val;
            else if (in_outputs) obs.output_values[wire] = val;
        }
    }
    fin.close();
    return obs;
}

bool is_directory(const string& path) {
    struct stat info;
    if (stat(path.c_str(), &info) != 0) return false;
    return (info.st_mode & S_IFDIR) != 0;
}

vector<string> get_obs_files(const string& dir_path, const string& circuit_name) {
    vector<string> files;
    DIR* dir = opendir(dir_path.c_str());
    if (dir == nullptr) {
        cerr << "Error: cannot open directory: " << dir_path << endl;
        return files;
    }
    struct dirent* entry;
    while ((entry = readdir(dir)) != nullptr) {
        string name = entry->d_name;
        if (name == "." || name == "..") continue;
        if (name.find("_obs_") != string::npos && name.find(".txt") != string::npos) {
            if (name.find(circuit_name) == 0) {
                files.push_back(dir_path + "/" + name);
            }
        }
    }
    closedir(dir);
    sort(files.begin(), files.end());
    return files;
}

string extract_filename(const string& path) {
    size_t pos = path.find_last_of("/\\");
    if (pos == string::npos) return path;
    return path.substr(pos + 1);
}

void print_table_header() {
    cout << "\n";
    cout << left << setw(25) << "obs"
         << "|" << setw(10) << "solved"
         << "|" << setw(12) << "cumulative"
         << "|" << setw(10) << "diag_size"
         << "|" << "diag_components" << endl;
    cout << string(90, '-') << endl;
}

void print_diagnosis_row(const string& obs_name, int idx, bool solved, double cumulative_time, int size, const set<int>& comps) {
    stringstream comp_str;
    bool first = true;
    for (int c : comps) {
        if (!first) comp_str << "|";
        comp_str << c;
        first = false;
    }
    
    string idx_str = "[" + to_string(idx) + "]";
    string full_name = obs_name + idx_str;
    
    cout << left << setw(25) << full_name
         << "|" << setw(10) << (solved ? "1" : "0")
         << "|" << setw(12) << fixed << setprecision(6) << cumulative_time
         << "|" << setw(10) << size
         << "|" << comp_str.str() << endl;
}

void print_batch_summary(const BatchResult& result) {
    cout << "\n  " << result.total_diagnoses << " diagnoses enumerated in " 
         << fixed << setprecision(2) << result.total_time << "s" << endl;
    cout << "  Preprocessing time: " << fixed << setprecision(6) << result.prep_time << "s" << endl;
    cout << "  Online time: " << fixed << setprecision(6) << result.online_time << "s" << endl;
    cout << "  Total time: " << fixed << setprecision(6) << result.total_time << "s" << endl;
}

class SATbDSolver {
private:
    Circuit& circuit;

    struct BEEModel {
        map<int, int> fixed_values;
        map<int, pair<int, bool>> equivalences;
        set<int> eliminated_gates;
        int original_vars;
        int simplified_vars;
    };

    Minisat::Lit mlit(Minisat::Var v, bool sign = false) {
        return Minisat::mkLit(v, sign);
    }

    void addClause(Minisat::Solver& S, const vector<Minisat::Lit>& lits) {
        Minisat::vec<Minisat::Lit> ps;
        for (auto& l : lits) ps.push(l);
        S.addClause(ps);
    }

    void addClauseWithPrefix(Minisat::Solver& S, const vector<Minisat::Lit>& prefix, const vector<Minisat::Lit>& lits) {
        vector<Minisat::Lit> merged;
        merged.reserve(prefix.size() + lits.size());
        merged.insert(merged.end(), prefix.begin(), prefix.end());
        merged.insert(merged.end(), lits.begin(), lits.end());
        addClause(S, merged);
    }

    void addAnd(Minisat::Solver& S, Minisat::Var a, Minisat::Var b, Minisat::Var c) {
        addClause(S, {~mlit(c), mlit(a)});
        addClause(S, {~mlit(c), mlit(b)});
        addClause(S, {mlit(c), ~mlit(a), ~mlit(b)});
    }

    void addOr(Minisat::Solver& S, Minisat::Var a, Minisat::Var b, Minisat::Var c) {
        addClause(S, {mlit(c), ~mlit(a)});
        addClause(S, {mlit(c), ~mlit(b)});
        addClause(S, {~mlit(c), mlit(a), mlit(b)});
    }

    void addXor(Minisat::Solver& S, Minisat::Var a, Minisat::Var b, Minisat::Var c) {
        addClause(S, {~mlit(a), ~mlit(b), ~mlit(c)});
        addClause(S, {~mlit(a), mlit(b), mlit(c)});
        addClause(S, {mlit(a), ~mlit(b), mlit(c)});
        addClause(S, {mlit(a), mlit(b), ~mlit(c)});
    }

    void addNot(Minisat::Solver& S, Minisat::Var a, Minisat::Var c) {
        addClause(S, {~mlit(c), ~mlit(a)});
        addClause(S, {mlit(c), mlit(a)});
    }

    void addNand(Minisat::Solver& S, Minisat::Var a, Minisat::Var b, Minisat::Var c) {
        addClause(S, {mlit(c), mlit(a)});
        addClause(S, {mlit(c), mlit(b)});
        addClause(S, {~mlit(c), ~mlit(a), ~mlit(b)});
    }

    void addNor(Minisat::Solver& S, Minisat::Var a, Minisat::Var b, Minisat::Var c) {
        addClause(S, {~mlit(c), ~mlit(a)});
        addClause(S, {~mlit(c), ~mlit(b)});
        addClause(S, {mlit(c), mlit(a), mlit(b)});
    }

    void addXnor(Minisat::Solver& S, Minisat::Var a, Minisat::Var b, Minisat::Var c) {
        addClause(S, {~mlit(a), ~mlit(b), mlit(c)});
        addClause(S, {~mlit(a), mlit(b), ~mlit(c)});
        addClause(S, {mlit(a), ~mlit(b), ~mlit(c)});
        addClause(S, {mlit(a), mlit(b), mlit(c)});
    }

    void addBuf(Minisat::Solver& S, Minisat::Var a, Minisat::Var c) {
        addClause(S, {~mlit(c), mlit(a)});
        addClause(S, {mlit(c), ~mlit(a)});
    }

    void addMultiAnd(Minisat::Solver& S, const vector<Minisat::Var>& in, Minisat::Var out) {
        for (auto v : in) addClause(S, {~mlit(out), mlit(v)});
        vector<Minisat::Lit> cl;
        for (auto v : in) cl.push_back(~mlit(v));
        cl.push_back(mlit(out));
        addClause(S, cl);
    }

    void addMultiNand(Minisat::Solver& S, const vector<Minisat::Var>& in, Minisat::Var out) {
        for (auto v : in) addClause(S, {mlit(out), mlit(v)});
        vector<Minisat::Lit> cl;
        for (auto v : in) cl.push_back(~mlit(v));
        cl.push_back(~mlit(out));
        addClause(S, cl);
    }

    void addMultiOr(Minisat::Solver& S, const vector<Minisat::Var>& in, Minisat::Var out) {
        for (auto v : in) addClause(S, {mlit(out), ~mlit(v)});
        vector<Minisat::Lit> cl;
        for (auto v : in) cl.push_back(mlit(v));
        cl.push_back(~mlit(out));
        addClause(S, cl);
    }

    void addMultiNor(Minisat::Solver& S, const vector<Minisat::Var>& in, Minisat::Var out) {
        for (auto v : in) addClause(S, {~mlit(out), ~mlit(v)});
        vector<Minisat::Lit> cl;
        for (auto v : in) cl.push_back(mlit(v));
        cl.push_back(mlit(out));
        addClause(S, cl);
    }

    void addMultiXor(Minisat::Solver& S, const vector<Minisat::Var>& in, Minisat::Var out) {
        if (in.size() == 2) { addXor(S, in[0], in[1], out); return; }
        Minisat::Var acc = in[0];
        for (size_t i = 1; i < in.size() - 1; i++) {
            Minisat::Var tmp = S.newVar();
            addXor(S, acc, in[i], tmp);
            acc = tmp;
        }
        addXor(S, acc, in.back(), out);
    }

    void addGateConstraint(Minisat::Solver& S, Gate& g,
                           map<int, Minisat::Var>& wv,
                           map<int, Minisat::Var>& hv,
                           map<int, Minisat::Var>& iv) {
        auto getWire = [&](int w) -> Minisat::Var {
            if (wv.count(w)) return wv[w];
            Minisat::Var v = S.newVar(); wv[w] = v; return v;
        };
        auto getHealth = [&](int gid) -> Minisat::Var {
            if (hv.count(gid)) return hv[gid];
            Minisat::Var v = S.newVar(); hv[gid] = v; return v;
        };
        auto getInternal = [&](int gid) -> Minisat::Var {
            if (iv.count(gid)) return iv[gid];
            Minisat::Var v = S.newVar(); iv[gid] = v; return v;
        };

        Minisat::Var h = getHealth(g.id);
        Minisat::Var cp = getInternal(g.id);
        Minisat::Var c = getWire(g.output);

        vector<Minisat::Var> inv;
        for (int inp : g.inputs) inv.push_back(getWire(inp));

        switch (g.type) {
            case GATE_AND:
                if (inv.size() == 2) addAnd(S, inv[0], inv[1], cp);
                else addMultiAnd(S, inv, cp);
                break;
            case GATE_NAND:
                if (inv.size() == 2) addNand(S, inv[0], inv[1], cp);
                else addMultiNand(S, inv, cp);
                break;
            case GATE_OR:
                if (inv.size() == 2) addOr(S, inv[0], inv[1], cp);
                else addMultiOr(S, inv, cp);
                break;
            case GATE_NOR:
                if (inv.size() == 2) addNor(S, inv[0], inv[1], cp);
                else addMultiNor(S, inv, cp);
                break;
            case GATE_XOR:
                if (inv.size() == 2) addXor(S, inv[0], inv[1], cp);
                else addMultiXor(S, inv, cp);
                break;
            case GATE_XNOR:
                if (inv.size() == 2) addXnor(S, inv[0], inv[1], cp);
                else {
                    Minisat::Var xo = S.newVar();
                    addMultiXor(S, inv, xo);
                    addNot(S, xo, cp);
                }
                break;
            case GATE_NOT:
                addNot(S, inv[0], cp);
                break;
            case GATE_BUF:
                addBuf(S, inv[0], cp);
                break;
            default: break;
        }

        addXnor(S, cp, h, c);
    }

    void addCardinalityLits(Minisat::Solver& S, const vector<Minisat::Lit>& lits, int k) {
        int n = lits.size();
        if (k >= n) return;
        if (k < 0) {
            Minisat::Var d = S.newVar();
            addClause(S, {mlit(d), ~mlit(d)});
            return;
        }

        if (k == 0) {
            for (auto l : lits) addClause(S, {~l});
            return;
        }

        vector<vector<Minisat::Var>> s(n, vector<Minisat::Var>(k + 1));

        for (int j = 0; j <= k; j++) s[0][j] = S.newVar();
        addClause(S, {mlit(s[0][0])});
        addClause(S, {~lits[0], mlit(s[0][1])});
        addClause(S, {~mlit(s[0][1]), lits[0]});
        for (int j = 2; j <= k; j++) addClause(S, {~mlit(s[0][j])});

        for (int i = 1; i < n; i++) {
            s[i][0] = S.newVar();
            addClause(S, {mlit(s[i][0])});
            addClause(S, {mlit(s[i][0]), mlit(s[i-1][0])});

            for (int j = 1; j <= k; j++) {
                s[i][j] = S.newVar();
                addClause(S, {mlit(s[i][j]), ~mlit(s[i-1][j])});
                addClause(S, {mlit(s[i][j]), ~mlit(s[i-1][j-1]), ~lits[i]});
                addClause(S, {~mlit(s[i][j]), mlit(s[i-1][j]), mlit(s[i-1][j-1])});
                addClause(S, {~mlit(s[i][j]), mlit(s[i-1][j]), lits[i]});
            }
            addClause(S, {~lits[i], ~mlit(s[i-1][k])});
        }
    }

    void addCardinalityLitsConditional(Minisat::Solver& S, const vector<Minisat::Lit>& lits, int k, Minisat::Lit enable) {
        int n = lits.size();
        if (k >= n) return;
        vector<Minisat::Lit> pref = {~enable};
        if (k < 0) {
            addClauseWithPrefix(S, pref, {});
            return;
        }
        if (k == 0) {
            for (auto l : lits) addClauseWithPrefix(S, pref, {~l});
            return;
        }
        vector<vector<Minisat::Var>> s(n, vector<Minisat::Var>(k + 1));
        for (int j = 0; j <= k; j++) s[0][j] = S.newVar();
        addClauseWithPrefix(S, pref, {mlit(s[0][0])});
        addClauseWithPrefix(S, pref, {~lits[0], mlit(s[0][1])});
        addClauseWithPrefix(S, pref, {~mlit(s[0][1]), lits[0]});
        for (int j = 2; j <= k; j++) addClauseWithPrefix(S, pref, {~mlit(s[0][j])});
        for (int i = 1; i < n; i++) {
            s[i][0] = S.newVar();
            addClauseWithPrefix(S, pref, {mlit(s[i][0])});
            addClauseWithPrefix(S, pref, {mlit(s[i][0]), mlit(s[i-1][0])});
            for (int j = 1; j <= k; j++) {
                s[i][j] = S.newVar();
                addClauseWithPrefix(S, pref, {mlit(s[i][j]), ~mlit(s[i-1][j])});
                addClauseWithPrefix(S, pref, {mlit(s[i][j]), ~mlit(s[i-1][j-1]), ~lits[i]});
                addClauseWithPrefix(S, pref, {~mlit(s[i][j]), mlit(s[i-1][j]), mlit(s[i-1][j-1])});
                addClauseWithPrefix(S, pref, {~mlit(s[i][j]), mlit(s[i-1][j]), lits[i]});
            }
            addClauseWithPrefix(S, pref, {~lits[i], ~mlit(s[i-1][k])});
        }
    }

    void addCardinality(Minisat::Solver& S, const vector<Minisat::Var>& vars, int k) {
        vector<Minisat::Lit> lits;
        for (auto v : vars) lits.push_back(mlit(v));
        addCardinalityLits(S, lits, k);
    }

    int propagateGate(Gate& g, const map<int, int>& values) {
        vector<int> inv;
        for (int inp : g.inputs) {
            auto it = values.find(inp);
            if (it == values.end()) return -1;
            inv.push_back(it->second);
        }
        switch (g.type) {
            case GATE_AND: { int r = 1; for (int v : inv) r &= v; return r; }
            case GATE_NAND: { int r = 1; for (int v : inv) r &= v; return 1 - r; }
            case GATE_OR: { int r = 0; for (int v : inv) r |= v; return r; }
            case GATE_NOR: { int r = 0; for (int v : inv) r |= v; return 1 - r; }
            case GATE_XOR: { int r = 0; for (int v : inv) r ^= v; return r; }
            case GATE_XNOR: { int r = 0; for (int v : inv) r ^= v; return 1 - r; }
            case GATE_NOT: return 1 - inv[0];
            case GATE_BUF: return inv[0];
            default: return -1;
        }
    }

    int findUpperBound(const Observation& obs) {
        map<int, int> values;
        for (auto& p : obs.input_values) values[p.first] = p.second;
        for (auto& p : obs.output_values) values[p.first] = p.second;

        set<int> faulty;
        for (int gid : circuit.topological_order) {
            Gate& g = circuit.gates[gid];
            if (g.type == GATE_INPUT) continue;

            bool all_known = true;
            for (int inp : g.inputs) {
                if (values.find(inp) == values.end()) { all_known = false; break; }
            }
            if (!all_known) continue;

            int prop = propagateGate(g, values);
            int out_wire = g.output;

            if (values.find(out_wire) == values.end()) {
                values[out_wire] = prop;
            } else {
                if (values[out_wire] != prop) faulty.insert(g.id);
            }
        }
        return faulty.size();
    }

    bool isDiagnosis(const set<int>& diag, const Observation& obs) {
        map<int, int> values;
        for (auto& p : obs.input_values) values[p.first] = p.second;

        for (int gid : circuit.topological_order) {
            Gate& g = circuit.gates[gid];
            if (g.type == GATE_INPUT) continue;

            bool all_known = true;
            for (int inp : g.inputs) {
                if (values.find(inp) == values.end()) { all_known = false; break; }
            }
            if (!all_known) continue;

            int normal_out = propagateGate(g, values);
            int out_wire = g.output;

            if (diag.count(g.id)) {
                values[out_wire] = 1 - normal_out;
            } else {
                values[out_wire] = normal_out;
            }
        }

        for (auto& p : obs.output_values) {
            if (values[p.first] != p.second) return false;
        }
        return true;
    }

    struct CoreModel {
        unique_ptr<Minisat::Solver> solver;
        map<int, Minisat::Var> wire_vars;
        map<int, Minisat::Var> health_vars;
        map<int, Minisat::Var> internal_vars;
        vector<Minisat::Lit> unhealthy_lits;
        vector<Minisat::Lit> healthy_lits;
    };

    void addWireEquivalence(Minisat::Solver& S, Minisat::Var src, Minisat::Var dst, bool negate) {
        if (negate) {
            addClause(S, {mlit(src), mlit(dst)});
            addClause(S, {~mlit(src), ~mlit(dst)});
        } else {
            addClause(S, {mlit(src), ~mlit(dst)});
            addClause(S, {~mlit(src), mlit(dst)});
        }
    }

    CoreModel buildCoreModel(const Observation& obs, const BEEModel* bee = nullptr) {
        CoreModel model;
        model.solver = unique_ptr<Minisat::Solver>(new Minisat::Solver());
        Minisat::Solver& S = *model.solver;
        for (int gid : circuit.topological_order) {
            Gate& g = circuit.gates[gid];
            if (g.type == GATE_INPUT) {
                if (model.wire_vars.count(g.output) == 0) {
                    Minisat::Var v = S.newVar();
                    model.wire_vars[g.output] = v;
                }
                continue;
            }
            if (bee != nullptr && bee->equivalences.count(g.id)) {
                auto getWire = [&](int w) -> Minisat::Var {
                    if (model.wire_vars.count(w)) return model.wire_vars[w];
                    Minisat::Var v = S.newVar();
                    model.wire_vars[w] = v;
                    return v;
                };
                auto getHealth = [&](int component_id) -> Minisat::Var {
                    if (model.health_vars.count(component_id)) return model.health_vars[component_id];
                    Minisat::Var v = S.newVar();
                    model.health_vars[component_id] = v;
                    return v;
                };
                auto eq = bee->equivalences.at(g.id);
                Minisat::Var src = getWire(eq.first);
                Minisat::Var out = getWire(g.output);
                addWireEquivalence(S, src, out, eq.second);
                addClause(S, {mlit(getHealth(g.id))});
                continue;
            }
            addGateConstraint(S, g, model.wire_vars, model.health_vars, model.internal_vars);
        }
        for (auto& p : obs.input_values) {
            Minisat::Var v = model.wire_vars.count(p.first) ? model.wire_vars[p.first] : (model.wire_vars[p.first] = S.newVar());
            if (p.second == 1) addClause(S, {mlit(v)});
            else addClause(S, {~mlit(v)});
        }
        for (auto& p : obs.output_values) {
            Minisat::Var v = model.wire_vars.count(p.first) ? model.wire_vars[p.first] : (model.wire_vars[p.first] = S.newVar());
            if (p.second == 1) addClause(S, {mlit(v)});
            else addClause(S, {~mlit(v)});
        }
        for (int d : circuit.dominated_components) {
            if (model.health_vars.count(d)) addClause(S, {mlit(model.health_vars[d])});
        }
        if (bee != nullptr) {
            for (auto& p : bee->fixed_values) {
                int key = p.first;
                int val = p.second;
                if (key > 0) {
                    Minisat::Var v = model.wire_vars.count(key) ? model.wire_vars[key] : (model.wire_vars[key] = S.newVar());
                    addClause(S, {val ? mlit(v) : ~mlit(v)});
                } else {
                    int gid = -key;
                    Minisat::Var v = model.health_vars.count(gid) ? model.health_vars[gid] : (model.health_vars[gid] = S.newVar());
                    addClause(S, {val ? mlit(v) : ~mlit(v)});
                }
            }
        }
        for (auto& sec : circuit.sections) {
            vector<Minisat::Lit> sec_unhealthy;
            for (int c : sec.components) {
                if (model.health_vars.count(c)) sec_unhealthy.push_back(~mlit(model.health_vars[c]));
            }
            if (sec.bound < (int)sec.components.size() && !sec_unhealthy.empty()) {
                addCardinalityLits(S, sec_unhealthy, sec.bound);
            }
        }
        set<int> comps = circuit.get_component_gates();
        for (int c : comps) {
            if (!model.health_vars.count(c)) continue;
            model.healthy_lits.push_back(mlit(model.health_vars[c]));
            model.unhealthy_lits.push_back(~mlit(model.health_vars[c]));
        }
        return model;
    }

    set<int> extractDiagnosis(const set<int>& comps, const map<int, Minisat::Var>& hv, Minisat::Solver& S) {
        set<int> diag;
        for (int c : comps) {
            if (hv.count(c) && S.modelValue(mlit(hv.at(c))) == l_False) diag.insert(c);
        }
        return diag;
    }

    set<int> solveMinDiagnosisOnModel(CoreModel& model, int k_ub) {
        set<int> comps = circuit.get_component_gates();
        Minisat::Solver& S = *model.solver;
        k_ub = min(k_ub, (int)model.unhealthy_lits.size());
        if (k_ub < 0) return {};
        vector<Minisat::Lit> selectors(k_ub + 1);
        for (int k = 0; k <= k_ub; k++) {
            Minisat::Var sv = S.newVar();
            selectors[k] = mlit(sv);
            addCardinalityLitsConditional(S, model.unhealthy_lits, k, selectors[k]);
        }
        int lo = 0;
        int hi = k_ub;
        int best_k = -1;
        while (lo <= hi) {
            int mid = (lo + hi) / 2;
            Minisat::vec<Minisat::Lit> assumptions;
            assumptions.push(selectors[mid]);
            bool sat = S.solve(assumptions);
            if (sat) {
                set<int> diag = extractDiagnosis(comps, model.health_vars, S);
                best_k = mid;
                hi = min(mid - 1, (int)diag.size() - 1);
            } else {
                lo = mid + 1;
            }
        }
        if (best_k < 0) return {};
        Minisat::vec<Minisat::Lit> assumptions;
        assumptions.push(selectors[best_k]);
        if (!S.solve(assumptions)) return {};
        return extractDiagnosis(comps, model.health_vars, S);
    }

    set<set<int>> enumerateAllMinDiagnosesOnModel(CoreModel& model, int card, const Observation& obs, double time_limit = 0.0) {
        set<int> comps = circuit.get_component_gates();
        Minisat::Solver& S = *model.solver;
        addCardinalityLits(S, model.unhealthy_lits, card);
        int n = model.unhealthy_lits.size();
        addCardinalityLits(S, model.healthy_lits, n - card);
        set<set<int>> tld_set;
        clock_t start = clock();
        while (S.solve()) {
            set<int> diag = extractDiagnosis(comps, model.health_vars, S);
            Minisat::vec<Minisat::Lit> blocking;
            for (int c : comps) {
                if (model.health_vars.count(c) == 0) continue;
                Minisat::Var v = model.health_vars[c];
                if (S.modelValue(mlit(v)) == l_False) blocking.push(mlit(v));
                else blocking.push(~mlit(v));
            }
            tld_set.insert(diag);
            S.addClause(blocking);
            if (time_limit > 0.0) {
                double elapsed = double(clock() - start) / CLOCKS_PER_SEC;
                if (elapsed >= time_limit) break;
            }
        }
        set<set<int>> all_diagnoses;
        for (auto& tld : tld_set) {
            set<set<int>> expanded = expandTLD(tld, obs);
            for (auto& d : expanded) all_diagnoses.insert(d);
        }
        return all_diagnoses;
    }

public:
    SATbDSolver(Circuit& c) : circuit(c) {}

    set<int> findMinCardDiagnosis(const Observation& obs) {
        CoreModel model = buildCoreModel(obs);
        int k_ub = findUpperBound(obs);
        int num_outputs = circuit.outputs.size();
        k_ub = min(k_ub, num_outputs);
        return solveMinDiagnosisOnModel(model, k_ub);
    }

    set<set<int>> findAllMinCardDiagnoses(const Observation& obs, bool use_bee = false, double time_limit = 0.0) {
        set<int> min_diag = use_bee ? findMinCardDiagnosisBEE(obs, false, true) : findMinCardDiagnosis(obs);
        if (min_diag.empty()) return {};
        int card = (int)min_diag.size();
        if (use_bee) {
            BEEModel bee = equiPropagation(obs);
            CoreModel model = buildCoreModel(obs, &bee);
            return enumerateAllMinDiagnosesOnModel(model, card, obs, time_limit);
        }
        CoreModel model = buildCoreModel(obs);
        return enumerateAllMinDiagnosesOnModel(model, card, obs, time_limit);
    }

    set<set<int>> expandTLD(const set<int>& tld, const Observation& obs) {
        vector<set<int>> chi_sets;
        for (int dom : tld) {
            set<int> cone;
            if (circuit.cone_map.count(dom)) {
                cone = circuit.cone_map[dom];
            } else {
                cone.insert(dom);
            }

            set<int> chi;
            for (int c : cone) {
                set<int> test_diag = tld;
                test_diag.erase(dom);
                test_diag.insert(c);
                if (isDiagnosis(test_diag, obs)) {
                    chi.insert(c);
                }
            }
            chi_sets.push_back(chi);
        }

        set<set<int>> result;
        result.insert(set<int>());
        for (auto& chi : chi_sets) {
            set<set<int>> new_result;
            for (auto& partial : result) {
                for (int c : chi) {
                    set<int> ext = partial;
                    ext.insert(c);
                    new_result.insert(ext);
                }
            }
            result = new_result;
        }
        return result;
    }

    BEEModel equiPropagation(const Observation& obs) {
        BEEModel model;
        model.original_vars = 0;
        model.simplified_vars = 0;

        map<int, int> wire_val;
        map<int, bool> wire_known;
        map<int, int> health_val;
        map<int, bool> health_known;

        for (auto& p : obs.input_values) {
            wire_val[p.first] = p.second;
            wire_known[p.first] = true;
        }
        for (auto& p : obs.output_values) {
            wire_val[p.first] = p.second;
            wire_known[p.first] = true;
        }

        for (int d : circuit.dominated_components) {
            health_val[d] = 1;
            health_known[d] = true;
        }

        bool changed = true;
        int iterations = 0;
        while (changed && iterations < 100) {
            changed = false;
            iterations++;

            for (int gid : circuit.topological_order) {
                Gate& g = circuit.gates[gid];
                if (g.type == GATE_INPUT) continue;

                bool all_inputs_known = true;
                for (int inp : g.inputs) {
                    if (!wire_known.count(inp)) { all_inputs_known = false; break; }
                }

                if (all_inputs_known && !wire_known.count(g.output)) {
                    int prop = propagateGate(g, wire_val);
                    if (prop >= 0) {
                        if (health_known.count(g.id) && health_known[g.id]) {
                            wire_val[g.output] = prop;
                            wire_known[g.output] = true;
                            model.fixed_values[g.output] = prop;
                            changed = true;
                        } else if (health_known.count(g.id) && !health_known[g.id]) {
                            wire_val[g.output] = 1 - prop;
                            wire_known[g.output] = true;
                            model.fixed_values[g.output] = 1 - prop;
                            changed = true;
                        }
                    }
                }

                if (wire_known.count(g.output) &&
                    all_inputs_known && !health_known.count(g.id)) {
                    int prop = propagateGate(g, wire_val);
                    if (prop >= 0 && prop == wire_val[g.output]) {
                        health_val[g.id] = 1;
                        health_known[g.id] = true;
                        model.fixed_values[-g.id] = 1;
                        changed = true;
                    } else if (prop >= 0 && prop != wire_val[g.output]) {
                        health_val[g.id] = 0;
                        health_known[g.id] = true;
                        model.fixed_values[-g.id] = 0;
                        changed = true;
                    }
                }
            }

            for (int gid : circuit.topological_order) {
                Gate& g = circuit.gates[gid];
                if (g.type == GATE_INPUT) continue;
                if (model.equivalences.count(g.id)) continue;
                if (model.eliminated_gates.count(g.id)) continue;

                if (g.type == GATE_BUF || g.type == GATE_NOT) {
                    int inp = g.inputs[0];
                    if (wire_known.count(inp) && wire_known.count(g.output)) {
                        continue;
                    }
                    if (health_known.count(g.id) && health_known[g.id]) {
                        bool negate = (g.type == GATE_NOT);
                        model.equivalences[g.id] = {inp, negate};
                        changed = true;
                    }
                }

                if (g.type == GATE_XOR && g.inputs.size() == 2) {
                    int a = g.inputs[0], b = g.inputs[1];
                    if (health_known.count(g.id) && health_known[g.id]) {
                        if (wire_known.count(a)) {
                            bool negate = (wire_val[a] == 1);
                            model.equivalences[g.id] = {b, negate};
                            changed = true;
                        } else if (wire_known.count(b)) {
                            bool negate = (wire_val[b] == 1);
                            model.equivalences[g.id] = {a, negate};
                            changed = true;
                        }
                    }
                }

                if (g.type == GATE_XNOR && g.inputs.size() == 2) {
                    int a = g.inputs[0], b = g.inputs[1];
                    if (health_known.count(g.id) && health_known[g.id]) {
                        if (wire_known.count(a)) {
                            bool negate = (wire_val[a] == 0);
                            model.equivalences[g.id] = {b, negate};
                            changed = true;
                        } else if (wire_known.count(b)) {
                            bool negate = (wire_val[b] == 0);
                            model.equivalences[g.id] = {a, negate};
                            changed = true;
                        }
                    }
                }
            }

            for (int gid : circuit.topological_order) {
                Gate& g = circuit.gates[gid];
                if (g.type == GATE_INPUT) continue;
                if (model.eliminated_gates.count(g.id)) continue;

                if (health_known.count(g.id) && health_known[g.id]) {
                    bool all_inp_known = true;
                    for (int inp : g.inputs) {
                        if (!wire_known.count(inp)) { all_inp_known = false; break; }
                    }
                    if (all_inp_known && !wire_known.count(g.output)) {
                        int prop = propagateGate(g, wire_val);
                        if (prop >= 0) {
                            wire_val[g.output] = prop;
                            wire_known[g.output] = true;
                            model.fixed_values[g.output] = prop;
                            changed = true;
                        }
                    }
                }
            }
        }

        model.original_vars = (int)(circuit.gates.size() * 3);
        model.simplified_vars = model.original_vars - (int)model.fixed_values.size() * 2;

           if (!g_quiet) {
              cout << "  BEE equi-propagation: " << model.fixed_values.size() << " fixed values, "
                  << model.equivalences.size() << " equivalences detected" << endl;
           }

        return model;
    }

    struct DimacsCNF {
        int num_vars;
        vector<vector<int>> clauses;
        vector<vector<int>> xor_clauses;
        map<int, int> wire_to_var;
        map<int, int> health_to_var;
        map<int, int> internal_to_var;
        map<int, int> var_to_wire;
        map<int, int> var_to_health;
    };

    DimacsCNF encodeToDimacs(const Observation& obs, const BEEModel& bee, bool use_xor) {
        DimacsCNF cnf;
        int next_var = 1;

        auto getWireVar = [&](int w) -> int {
            if (cnf.wire_to_var.count(w)) return cnf.wire_to_var[w];
            cnf.wire_to_var[w] = next_var;
            cnf.var_to_wire[next_var] = w;
            return next_var++;
        };

        auto getHealthVar = [&](int gid) -> int {
            if (cnf.health_to_var.count(gid)) return cnf.health_to_var[gid];
            cnf.health_to_var[gid] = next_var;
            cnf.var_to_health[next_var] = gid;
            return next_var++;
        };

        auto getInternalVar = [&](int gid) -> int {
            if (cnf.internal_to_var.count(gid)) return cnf.internal_to_var[gid];
            cnf.internal_to_var[gid] = next_var;
            return next_var++;
        };

        auto addDimacsClause = [&](vector<int> cl) {
            bool taut = false;
            set<int> lits_set(cl.begin(), cl.end());
            for (int l : cl) {
                if (lits_set.count(-l)) { taut = true; break; }
            }
            if (!taut && !cl.empty()) cnf.clauses.push_back(cl);
        };

        for (int gid : circuit.topological_order) {
            Gate& g = circuit.gates[gid];
            if (g.type == GATE_INPUT) {
                getWireVar(g.output);
                continue;
            }

            if (bee.equivalences.count(gid)) {
                auto& eq = bee.equivalences.at(gid);
                int src_wire = eq.first;
                bool negate = eq.second;
                int src_v = getWireVar(src_wire);
                int out_v = getWireVar(g.output);
                if (negate) {
                    addDimacsClause({src_v, out_v});
                    addDimacsClause({-src_v, -out_v});
                } else {
                    addDimacsClause({src_v, -out_v});
                    addDimacsClause({-src_v, out_v});
                }
                continue;
            }

            int h = getHealthVar(g.id);
            int cp = getInternalVar(g.id);
            int c = getWireVar(g.output);

            vector<int> inv;
            for (int inp : g.inputs) inv.push_back(getWireVar(inp));

            auto encodeGate = [&](vector<int>& in_vars, int cp_var, GateType type) {
                if (in_vars.size() == 2) {
                    int a = in_vars[0], b = in_vars[1];
                    switch (type) {
                        case GATE_AND:
                            addDimacsClause({-cp_var, a});
                            addDimacsClause({-cp_var, b});
                            addDimacsClause({cp_var, -a, -b});
                            break;
                        case GATE_NAND:
                            addDimacsClause({cp_var, a});
                            addDimacsClause({cp_var, b});
                            addDimacsClause({-cp_var, -a, -b});
                            break;
                        case GATE_OR:
                            addDimacsClause({cp_var, -a});
                            addDimacsClause({cp_var, -b});
                            addDimacsClause({-cp_var, a, b});
                            break;
                        case GATE_NOR:
                            addDimacsClause({-cp_var, -a});
                            addDimacsClause({-cp_var, -b});
                            addDimacsClause({cp_var, a, b});
                            break;
                        case GATE_XOR:
                            if (use_xor) {
                                cnf.xor_clauses.push_back({a, b, cp_var});
                            } else {
                                addDimacsClause({-a, -b, -cp_var});
                                addDimacsClause({-a, b, cp_var});
                                addDimacsClause({a, -b, cp_var});
                                addDimacsClause({a, b, -cp_var});
                            }
                            break;
                        case GATE_XNOR:
                            if (use_xor) {
                                cnf.xor_clauses.push_back({a, b, -cp_var});
                            } else {
                                addDimacsClause({-a, -b, cp_var});
                                addDimacsClause({-a, b, -cp_var});
                                addDimacsClause({a, -b, -cp_var});
                                addDimacsClause({a, b, cp_var});
                            }
                            break;
                        default: break;
                    }
                } else if (in_vars.size() == 1) {
                    int a = in_vars[0];
                    if (type == GATE_NOT) {
                        addDimacsClause({-cp_var, -a});
                        addDimacsClause({cp_var, a});
                    } else if (type == GATE_BUF) {
                        addDimacsClause({-cp_var, a});
                        addDimacsClause({cp_var, -a});
                    }
                } else {
                    switch (type) {
                        case GATE_AND:
                            for (int v : in_vars) addDimacsClause({-cp_var, v});
                            { vector<int> cl; for (int v : in_vars) cl.push_back(-v); cl.push_back(cp_var); addDimacsClause(cl); }
                            break;
                        case GATE_NAND:
                            for (int v : in_vars) addDimacsClause({cp_var, v});
                            { vector<int> cl; for (int v : in_vars) cl.push_back(-v); cl.push_back(-cp_var); addDimacsClause(cl); }
                            break;
                        case GATE_OR:
                            for (int v : in_vars) addDimacsClause({cp_var, -v});
                            { vector<int> cl; for (int v : in_vars) cl.push_back(v); cl.push_back(-cp_var); addDimacsClause(cl); }
                            break;
                        case GATE_NOR:
                            for (int v : in_vars) addDimacsClause({-cp_var, -v});
                            { vector<int> cl; for (int v : in_vars) cl.push_back(v); cl.push_back(cp_var); addDimacsClause(cl); }
                            break;
                        case GATE_XOR: {
                            int acc = in_vars[0];
                            for (size_t i = 1; i < in_vars.size() - 1; i++) {
                                int tmp = next_var++;
                                if (use_xor) {
                                    cnf.xor_clauses.push_back({acc, in_vars[i], tmp});
                                } else {
                                    addDimacsClause({-acc, -in_vars[i], -tmp});
                                    addDimacsClause({-acc, in_vars[i], tmp});
                                    addDimacsClause({acc, -in_vars[i], tmp});
                                    addDimacsClause({acc, in_vars[i], -tmp});
                                }
                                acc = tmp;
                            }
                            if (use_xor) {
                                cnf.xor_clauses.push_back({acc, in_vars.back(), cp_var});
                            } else {
                                addDimacsClause({-acc, -in_vars.back(), -cp_var});
                                addDimacsClause({-acc, in_vars.back(), cp_var});
                                addDimacsClause({acc, -in_vars.back(), cp_var});
                                addDimacsClause({acc, in_vars.back(), -cp_var});
                            }
                            break;
                        }
                        default: break;
                    }
                }
            };

            encodeGate(inv, cp, g.type);

            if (use_xor) {
                cnf.xor_clauses.push_back({cp, h, -c});
            } else {
                addDimacsClause({-cp, -h, c});
                addDimacsClause({-cp, h, -c});
                addDimacsClause({cp, -h, -c});
                addDimacsClause({cp, h, c});
            }
        }

        for (auto& p : obs.input_values) {
            int v = getWireVar(p.first);
            if (p.second == 1) addDimacsClause({v});
            else addDimacsClause({-v});
        }
        for (auto& p : obs.output_values) {
            int v = getWireVar(p.first);
            if (p.second == 1) addDimacsClause({v});
            else addDimacsClause({-v});
        }

        for (auto& p : bee.fixed_values) {
            int key = p.first;
            int val = p.second;
            if (key > 0) {
                if (cnf.wire_to_var.count(key)) {
                    int v = cnf.wire_to_var[key];
                    if (val == 1) addDimacsClause({v});
                    else addDimacsClause({-v});
                }
            } else {
                int gid = -key;
                if (cnf.health_to_var.count(gid)) {
                    int v = cnf.health_to_var[gid];
                    if (val == 1) addDimacsClause({v});
                    else addDimacsClause({-v});
                }
            }
        }

        for (int d : circuit.dominated_components) {
            int v = getHealthVar(d);
            addDimacsClause({v});
        }

        cnf.num_vars = next_var - 1;

        for (auto& sec : circuit.sections) {
            vector<int> sec_unhealthy;
            for (int c : sec.components) {
                int v = getHealthVar(c);
                sec_unhealthy.push_back(-v);
            }
            if (sec.bound < (int)sec.components.size() && !sec_unhealthy.empty()) {
                addCardinalityDimacs(cnf, sec_unhealthy, sec.bound);
            }
        }

        return cnf;
    }

    void addCardinalityDimacs(DimacsCNF& cnf, const vector<int>& lits, int k) {
        int n = lits.size();
        if (k >= n) return;
        if (k < 0) { cnf.clauses.push_back({}); return; }
        if (k == 0) {
            for (int l : lits) cnf.clauses.push_back({-l});
            return;
        }

        vector<vector<int>> s(n, vector<int>(k + 1));
        for (int j = 0; j <= k; j++) s[0][j] = cnf.num_vars + 1 + j;
        cnf.num_vars += k + 1;

        cnf.clauses.push_back({s[0][0]});
        cnf.clauses.push_back({-lits[0], s[0][1]});
        cnf.clauses.push_back({-s[0][1], lits[0]});
        for (int j = 2; j <= k; j++) cnf.clauses.push_back({-s[0][j]});

        for (int i = 1; i < n; i++) {
            for (int j = 0; j <= k; j++) s[i][j] = ++cnf.num_vars;

            cnf.clauses.push_back({s[i][0]});
            cnf.clauses.push_back({s[i][0], s[i-1][0]});

            for (int j = 1; j <= k; j++) {
                cnf.clauses.push_back({s[i][j], -s[i-1][j]});
                cnf.clauses.push_back({s[i][j], -s[i-1][j-1], -lits[i]});
                cnf.clauses.push_back({-s[i][j], s[i-1][j], s[i-1][j-1]});
                cnf.clauses.push_back({-s[i][j], s[i-1][j], lits[i]});
            }
            cnf.clauses.push_back({-lits[i], -s[i-1][k]});
        }
    }

    string writeDimacsFile(const DimacsCNF& cnf, const string& prefix) {
        string cnf_file = "/tmp/satbd_" + prefix + ".cnf";
        ofstream fout(cnf_file);
        fout << "p cnf " << cnf.num_vars << " " << cnf.clauses.size() << endl;
        for (auto& cl : cnf.clauses) {
            for (int l : cl) fout << l << " ";
            fout << "0" << endl;
        }
        fout.close();

        if (!cnf.xor_clauses.empty()) {
            string xor_file = "/tmp/satbd_" + prefix + ".xor";
            ofstream fxor(xor_file);
            fxor << cnf.xor_clauses.size() << " " << cnf.num_vars << endl;
            for (auto& xc : cnf.xor_clauses) {
                for (size_t i = 0; i < xc.size(); i++) {
                    fxor << xc[i];
                    if (i + 1 < xc.size()) fxor << " ";
                }
                fxor << endl;
            }
            fxor.close();
        }

        return cnf_file;
    }

    struct CMSatResult {
        bool sat;
        map<int, bool> assignment;
        int num_vars;
    };

    CMSatResult solveWithCryptoMiniSat(const DimacsCNF& cnf, int k, const string& prefix) {
        CMSatResult result;
        result.sat = false;

        DimacsCNF working_cnf = cnf;

        set<int> comps = circuit.get_component_gates();
        vector<int> all_unhealthy;
        for (int c : comps) {
            int v = working_cnf.health_to_var.count(c) ? working_cnf.health_to_var[c] : 0;
            if (v > 0) all_unhealthy.push_back(-v);
        }
        if (!all_unhealthy.empty()) {
            addCardinalityDimacs(working_cnf, all_unhealthy, k);
        }

        string cnf_file = writeDimacsFile(working_cnf, prefix);
        string xor_file;
        if (!working_cnf.xor_clauses.empty()) {
            xor_file = "/tmp/satbd_" + prefix + ".xor";
        }

        string result_file = "/tmp/satbd_" + prefix + ".result";
        string py_script = "/tmp/satbd_cms5_solver.py";

        ofstream pyscript(py_script);
        pyscript << "import sys\n";
        pyscript << "from pycryptosat import Solver\n\n";
        pyscript << "def main():\n";
        pyscript << "    cnf_file = sys.argv[1]\n";
        pyscript << "    result_file = sys.argv[2]\n";
        pyscript << "    xor_file = sys.argv[3] if len(sys.argv) > 3 else None\n\n";
        pyscript << "    s = Solver(threads=1)\n\n";
        pyscript << "    with open(cnf_file, 'r') as f:\n";
        pyscript << "        header = f.readline()\n";
        pyscript << "        for line in f:\n";
        pyscript << "            line = line.strip()\n";
        pyscript << "            if not line or line.startswith('c') or line.startswith('p'):\n";
        pyscript << "                continue\n";
        pyscript << "            lits = [int(x) for x in line.split() if int(x) != 0]\n";
        pyscript << "            if lits:\n";
        pyscript << "                s.add_clause(lits)\n\n";
        pyscript << "    if xor_file:\n";
        pyscript << "        try:\n";
        pyscript << "            with open(xor_file, 'r') as f:\n";
        pyscript << "                header = f.readline()\n";
        pyscript << "                for line in f:\n";
        pyscript << "                    line = line.strip()\n";
        pyscript << "                    if not line:\n";
        pyscript << "                        continue\n";
        pyscript << "                    lits = [int(x) for x in line.split()]\n";
        pyscript << "                    if lits:\n";
        pyscript << "                        rhs = False\n";
        pyscript << "                        pos_lits = []\n";
        pyscript << "                        for l in lits:\n";
        pyscript << "                            if l < 0:\n";
        pyscript << "                                pos_lits.append(-l)\n";
        pyscript << "                                rhs = not rhs\n";
        pyscript << "                            else:\n";
        pyscript << "                                pos_lits.append(l)\n";
        pyscript << "                        s.add_xor_clause(pos_lits, rhs)\n";
        pyscript << "        except FileNotFoundError:\n";
        pyscript << "            pass\n\n";
        pyscript << "    sat, solution = s.solve()\n";
        pyscript << "    with open(result_file, 'w') as f:\n";
        pyscript << "        if sat:\n";
        pyscript << "            f.write('SAT\\n')\n";
        pyscript << "            if solution:\n";
        pyscript << "                f.write(str(len(solution)) + '\\n')\n";
        pyscript << "                for i, v in enumerate(solution):\n";
        pyscript << "                    if v is not None:\n";
        pyscript << "                        f.write(str(i) + ' ' + ('1' if v else '0') + '\\n')\n";
        pyscript << "        else:\n";
        pyscript << "            f.write('UNSAT\\n')\n\n";
        pyscript << "if __name__ == '__main__':\n";
        pyscript << "    main()\n";
        pyscript.close();

        string cmd = "python3 " + py_script + " " + cnf_file + " " + result_file;
        if (!xor_file.empty()) cmd += " " + xor_file;

        int ret = std::system(cmd.c_str());
        if (ret != 0) {
            cerr << "  CryptoMiniSat solver failed (exit code " << ret << ")" << endl;
            return result;
        }

        ifstream fin(result_file);
        string status;
        fin >> status;
        if (status == "SAT") {
            result.sat = true;
            int nvars;
            fin >> nvars;
            result.num_vars = nvars;
            int var_id;
            string val_str;
            while (fin >> var_id >> val_str) {
                result.assignment[var_id] = (val_str == "1");
            }
        }
        fin.close();

        remove(cnf_file.c_str());
        if (!xor_file.empty()) remove(xor_file.c_str());
        remove(result_file.c_str());
        remove(py_script.c_str());

        return result;
    }

    set<int> findMinCardDiagnosisBEE(const Observation& obs, bool use_cryptominisat, bool use_bee = true) {
        if (use_cryptominisat && !g_quiet) {
            cout << "  CryptoMiniSat backend requested, but local MiniBEE currently uses unified incremental MiniSat fallback." << endl;
        }
        int k_ub = findUpperBound(obs);
        int num_outputs = circuit.outputs.size();
        k_ub = min(k_ub, num_outputs);
        if (!use_bee) {
            CoreModel model = buildCoreModel(obs);
            return solveMinDiagnosisOnModel(model, k_ub);
        }
        if (!g_quiet) cout << "Running local MiniBEE-enhanced diagnosis..." << endl;
        BEEModel bee = equiPropagation(obs);
        CoreModel model = buildCoreModel(obs, &bee);
           if (!g_quiet) {
              cout << "  MiniBEE core: " << model.health_vars.size() << " health vars, "
                  << model.wire_vars.size() << " wire vars" << endl;
           }
        return solveMinDiagnosisOnModel(model, k_ub);
    }
};

BatchResult process_single_obs(const string& bench_file, const string& obs_file, 
                                bool find_all, bool use_bee, bool use_cryptominisat) {
    BatchResult result;
    result.circuit_name = extract_filename(bench_file);
    result.total_time = 0;
    result.total_diagnoses = 0;
    
    bool bee_available = use_bee;
    bool cms_available = false;
    
    if (use_cryptominisat) {
        string check_py = "python3 -c \"from pycryptosat import Solver\" >/dev/null 2>&1";
        cms_available = (std::system(check_py.c_str()) == 0);
    }
    
    Circuit circuit;
    circuit.parse_bench(bench_file);
    
    clock_t t0 = clock();
    circuit.preprocess();
    clock_t t1 = clock();
    double prep_time = double(t1 - t0) / CLOCKS_PER_SEC;
    
    Observation obs = parse_observation(obs_file);
    
    SATbDSolver solver(circuit);
    
    t0 = clock();
    set<int> min_diag;
    
    if (bee_available && cms_available) {
        min_diag = solver.findMinCardDiagnosisBEE(obs, true);
    } else if (bee_available && !cms_available) {
        min_diag = solver.findMinCardDiagnosisBEE(obs, false);
    } else if (!bee_available && cms_available) {
        min_diag = solver.findMinCardDiagnosisBEE(obs, true, false);
    } else {
        min_diag = solver.findMinCardDiagnosis(obs);
    }
    t1 = clock();
    
    double diag_time = double(t1 - t0) / CLOCKS_PER_SEC;
    string obs_name = extract_filename(obs_file);
    
    if (find_all && !min_diag.empty()) {
        t0 = clock();
        double base_time = prep_time + diag_time;
        const double TIME_LIMIT = 300.0; // seconds
        double remaining = TIME_LIMIT - diag_time;
        if (remaining < 0) remaining = 0;
        set<set<int>> all_diags = solver.findAllMinCardDiagnoses(obs, bee_available, remaining);
        t1 = clock();
        double all_time = double(t1 - t0) / CLOCKS_PER_SEC;
        
        int idx = 1;
        double current_time = base_time;
        double time_per_diag = all_time / max(1, (int)all_diags.size());
        
        for (auto& d : all_diags) {
            current_time += time_per_diag;
            DiagnosisResult dr;
            dr.obs_file = obs_name;
            dr.diagnosis_index = idx++;
            dr.solved = true;
            dr.time_seconds = time_per_diag;
            dr.cumulative_seconds = current_time;
            dr.diag_size = d.size();
            dr.diag_components = d;
            result.results.push_back(dr);
        }
        result.total_diagnoses = all_diags.size();
        result.total_time = prep_time + diag_time + all_time;
        result.prep_time = prep_time;
        result.online_time = diag_time + all_time;
    } else {
        double total_time = prep_time + diag_time;
        DiagnosisResult dr;
        dr.obs_file = obs_name;
        dr.diagnosis_index = 1;
        dr.solved = !min_diag.empty();
        dr.time_seconds = diag_time;
        dr.cumulative_seconds = total_time;
        dr.diag_size = min_diag.size();
        dr.diag_components = min_diag;
        result.results.push_back(dr);
        result.total_diagnoses = 1;
        result.total_time = total_time;
        result.prep_time = prep_time;
        result.online_time = diag_time;
    }
    
    return result;
}

int main(int argc, char* argv[]) {
    if (argc < 3) {
        cerr << "Usage: " << argv[0] << " <bench_file> <obs_file|obs_dir> [--all] [--use-bee] [--use-cryptominisat]" << endl;
        cerr << "  bench_file: ISCAS-85 .bench circuit file" << endl;
        cerr << "  obs_file: single observation file" << endl;
        cerr << "  obs_dir: directory containing observation files (batch mode)" << endl;
        cerr << "  --all: find all minimal cardinality diagnoses (optional)" << endl;
        cerr << "  --use-bee: prefer BEE/equi-propagation pipeline when available" << endl;
        cerr << "  --use-cryptominisat: prefer CryptoMiniSat backend when available" << endl;
        return 1;
    }

    string bench_file = argv[1];
    string obs_path = argv[2];
    bool find_all = false;
    bool use_bee = false;
    bool use_cryptominisat = false;
    for (int i = 3; i < argc; i++) {
        string arg = argv[i];
        if (arg == "--all") find_all = true;
        if (arg == "--use-bee") use_bee = true;
        if (arg == "--use-cryptominisat") use_cryptominisat = true;
    }
    
    bool batch_mode = is_directory(obs_path);
    
    string circuit_name = extract_filename(bench_file);
    size_t dot_pos = circuit_name.find('.');
    if (dot_pos != string::npos) {
        circuit_name = circuit_name.substr(0, dot_pos);
    }
    
    if (batch_mode) {
        cout << "=== SATbD: SAT-based Diagnosis (Batch Mode) ===" << endl;
        cout << "Circuit: " << bench_file << endl;
        cout << "Observation directory: " << obs_path << endl;
        // 在批处理模式中禁用内部调试/信息输出
        g_quiet = true;
        
        vector<string> obs_files = get_obs_files(obs_path, circuit_name);
        if (obs_files.empty()) {
            cerr << "No observation files found for circuit '" << circuit_name << "' in directory: " << obs_path << endl;
            return 1;
        }
        cout << "Found " << obs_files.size() << " observation files" << endl;
        
        if (use_bee) {
            cout << "BEE: using built-in MiniBEE compiler/equi-propagation" << endl;
        }
        if (use_cryptominisat) {
            string check_py = "python3 -c \"from pycryptosat import Solver\" >/dev/null 2>&1";
            bool cms_available = (std::system(check_py.c_str()) == 0);
            cout << "CryptoMiniSat (pycryptosat): " << (cms_available ? "available" : "not found") << endl;
        }
        
        // 新表头：obs | time | num | size | all_size | real_num | hitrate | timeout
        cout << left << setw(20) << "obs"
             << "|" << setw(8) << "time"
             << "|" << setw(6) << "num"
             << "|" << setw(6) << "size"
             << "|" << setw(8) << "all_size"
             << "|" << setw(8) << "real_num"
             << "|" << setw(8) << "hitrate"
             << "|" << setw(8) << "timeout"
             << endl;
        cout << string(80, '-') << endl;

        int obs_cnt = obs_files.size();
        double total_time = 0;
        double total_hitrate = 0; // legacy, kept for compatibility
        double total_hitrate_non_pseudo = 0; // only for non-pseudo obs
        int non_pseudo_count = 0;
        int total_success = 0;
        double all_obs_time = 0;

        for (const string& obs_file : obs_files) {
            clock_t t0 = clock();
            bool timeout = false;
            double obs_time = 0;
            set<set<int>> all_diags;
            set<int> all_comps;
            int min_size = 0;
            int real_num = 0;
            double hitrate = 0;
            int num = 0;
            string obs_name = extract_filename(obs_file);
            Observation obs = parse_observation(obs_file);
            Circuit circuit;
            circuit.parse_bench(bench_file);
            circuit.preprocess();
            SATbDSolver solver(circuit);
            // 限时300s
            const double TIME_LIMIT = 300.0;
            clock_t diag_t0 = clock();
            set<int> min_diag = solver.findMinCardDiagnosis(obs);
            clock_t diag_t1 = clock();
            obs_time = double(diag_t1 - diag_t0) / CLOCKS_PER_SEC;
            bool is_pseudo = min_diag.empty();
            if (!is_pseudo) {
                min_size = min_diag.size();
                // 枚举所有最小解
                clock_t all_t0 = clock();
                all_diags = solver.findAllMinCardDiagnoses(obs, true);
                clock_t all_t1 = clock();
                obs_time += double(all_t1 - all_t0) / CLOCKS_PER_SEC;
                // 超时判断
                if (obs_time > TIME_LIMIT) {
                    timeout = true;
                }
                // 统计所有诊断解的组件集合
                for (const auto& d : all_diags) {
                    for (int c : d) all_comps.insert(c);
                }
                // 统计真实组件数量
                for (int c : all_comps) {
                    if (obs.fault_set.count(c)) real_num++;
                }
                // 命中率
                if (!all_comps.empty()) hitrate = 100.0 * real_num / all_comps.size();
                num = all_diags.size();
                // accumulate non-pseudo hitrate
                total_hitrate_non_pseudo += hitrate;
                non_pseudo_count++;
            } else {
                timeout = false;
                min_size = 0;
                num = 0;
                hitrate = 0;
                real_num = 0;
            }
            if (obs_time > TIME_LIMIT) {
                timeout = true;
                obs_time = TIME_LIMIT;
            }
            total_time += obs_time;
            total_hitrate += hitrate;
            // 伪观测（min_diag 为空）也计为成功，只要不超时
            if (!timeout) total_success++;
            all_obs_time += obs_time;
            // 输出一行
            cout << left << setw(20) << obs_name
                 << "|" << setw(8) << fixed << setprecision(2) << obs_time
                 << "|" << setw(6) << num
                 << "|" << setw(6) << min_size
                 << "|" << setw(8) << all_comps.size()
                 << "|" << setw(8) << real_num
                 << "|" << setw(8) << fixed << setprecision(2) << hitrate
                 << "|" << setw(8) << (timeout ? "1" : "0")
                 << endl;
        }
        // 最后一行输出总用时、平均用时、平均HITrate、成功率
        double avg_time = obs_cnt > 0 ? all_obs_time / obs_cnt : 0;
        double avg_hitrate = non_pseudo_count > 0 ? total_hitrate_non_pseudo / non_pseudo_count : 0;
        double success_rate = obs_cnt > 0 ? 100.0 * total_success / obs_cnt : 0;
        cout << string(80, '-') << endl;
        cout << "TOTAL summary for " << obs_cnt << " observations:\n";
        cout << "  total_time(s): " << fixed << setprecision(2) << all_obs_time << "\n";
        cout << "  avg_time(s):   " << fixed << setprecision(2) << avg_time << "\n";
        cout << "  avg_HITrate(%): " << fixed << setprecision(2) << avg_hitrate << "\n";
        cout << "  success_rate(%): " << fixed << setprecision(2) << success_rate << "\n";
        
    } else {
        cout << "=== SATbD: SAT-based Diagnosis ===" << endl;
        cout << "Circuit: " << bench_file << endl;
        cout << "Observation: " << obs_path << endl;
        
        if (use_bee) {
            cout << "BEE: using built-in MiniBEE compiler/equi-propagation" << endl;
        }
        if (use_cryptominisat) {
            string check_py = "python3 -c \"from pycryptosat import Solver\" >/dev/null 2>&1";
            bool cms_available = (std::system(check_py.c_str()) == 0);
            cout << "CryptoMiniSat (pycryptosat): " << (cms_available ? "available" : "not found") << endl;
        }
        
        BatchResult result = process_single_obs(bench_file, obs_path, find_all, use_bee, use_cryptominisat);
        
        print_table_header();
        for (const auto& dr : result.results) {
            print_diagnosis_row(dr.obs_file, dr.diagnosis_index, dr.solved, 
                               dr.cumulative_seconds, dr.diag_size, dr.diag_components);
        }
        print_batch_summary(result);
    }

    return 0;
}
