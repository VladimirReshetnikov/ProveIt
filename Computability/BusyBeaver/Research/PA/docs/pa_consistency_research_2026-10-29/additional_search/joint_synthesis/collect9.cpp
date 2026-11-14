// Independent finite checks of a binary TM against its primitive source frames.
// These checks are regression evidence, not a quantified simulation theorem.
// Build: g++ -std=c++17 -O3 check_finite_runtime.cpp -o check_finite_runtime
// Run: ./check_finite_runtime machine.native.tm sites.tsv
#include <array>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Transition { int write, move, target; };
struct Site { string address, operation; int argument; };
array<array<Transition, 2>, 1000> machine;
long long primitive_steps = 0, case_count = 0;
constexpr int RAD=9;
array<set<int>,1000> contexts;

set<int> frame(string pc, vector<int> registers, vector<int> spares, int gap) {
    constexpr int physical[9] = {6, 2, 0, 4, 3, 7, 8, 5, 1};
    vector<int> values(9);
    for (int i = 0; i < 9; ++i) values[physical[i]] = registers[i];
    values.insert(values.end(), spares.begin(), spares.end());
    set<int> tape = {-1, 56 + gap};
    for (int i = 0; i < int(pc.size()); ++i) if (pc[i] == '1') tape.insert(i);
    int cursor = 57 + gap;
    for (int value : values) {
        for (int j = 1; j <= value + 1; ++j) tape.insert(cursor + j);
        cursor += value + 2;
    }
    return tape;
}
string strip(string pc, char bit, int count) {
    for (int i = int(pc.size()) - 1; i >= 0; --i)
        if (pc[i] == bit && --count == 0) return pc.substr(0, i);
    return "";
}
pair<string, int> increment(string pc) {
    for (int i = int(pc.size()) - 1; i >= 0; --i) {
        if (pc[i] == '0') { pc[i] = '1'; return {pc, 0}; }
        pc[i] = '0';
    }
    return {pc, 1};
}
void step(int& state, int& head, set<int>& tape) {
    int code=0; for(int i=-RAD;i<=RAD;i++) code |= int(tape.count(head+i)) << (i+RAD);
    contexts[state].insert(code);
    const auto transition = machine[state][tape.count(head)];
    if (transition.write) tape.insert(head); else tape.erase(head);
    head += transition.move;
    state = transition.target;
}
void check_case(const Site& site, vector<int> regs, vector<int> spares, int gap) {
    ++case_count;
    auto tape = frame(site.address, regs, spares, gap);
    string pc = site.address;
    int shift = 0, delta = 0;
    const auto& op = site.operation;
    if (op == "CI") {
        ++regs[site.argument];
        spares.push_back(1);
        tie(pc, shift) = increment(pc);
    } else if (op == "CD" && regs[site.argument] > 0) {
        --regs[site.argument]; delta = 1;
        tie(pc, shift) = increment(pc);
    } else if (op == "CD" || op == "CB") {
        tie(pc, shift) = increment(strip(pc, '0', op == "CD" ? 1 : site.argument));
    } else if (op == "CC") {
        pc = strip(pc, '1', site.argument);
    } else if (op != "CH") throw runtime_error("Unknown source opcode");
    auto unshifted = frame(pc, regs, spares, gap + delta + shift);
    set<int> expected;
    for (int position : unshifted) expected.insert(position - shift);
    int state = 84, head = 0;
    for (int tick = 0; tick <= 100000; ++tick) {
        if (tick > 0 && ((state == 254 && op == "CH") ||
            (op != "CH" && state == 84 && head == -shift && tape == expected))) {
            primitive_steps += tick;
            return;
        }
        if (tick == 100000 || state == 254)
            throw runtime_error("Primitive mismatch at " + site.address + " " + op);
        step(state, head, tape);
    }
    throw runtime_error("Unreachable checker branch");
}
int main(int argc, char** argv) {
    try {
        if (argc != 4) throw runtime_error("Expected machine.native.tm and sites.tsv");
        ifstream input(argv[1]);
        if (!input) throw runtime_error("Cannot open machine");
        string line;
        set<pair<int, int>> domains;
        while (getline(input, line)) {
            if (line.empty() || line[0] == '#') continue;
            int q, read, write, target; char direction;
            istringstream row(line);
            if (!(row >> q >> read >> write >> direction >> target) ||
                q < 0 || q >= 1000 || target < 0 || target >= 1000 ||
                (read != 0 && read != 1) || (write != 0 && write != 1) ||
                (direction != 'L' && direction != 'R') ||
                !domains.insert({q, read}).second) throw runtime_error("Invalid row");
            machine[q][read] = {write, direction == 'R' ? 1 : -1, target};
        }
        for (auto [q, read] : domains) {
            if (!domains.count({q, 1-read})) throw runtime_error("Incomplete state");
            int target = machine[q][read].target;
            if (target != 254 && !domains.count({target, 0}))
                throw runtime_error("Undefined working target");
        }
        ifstream source(argv[2]);
        if (!source) throw runtime_error("Cannot open source sites");
        vector<Site> sites;
        string address, operation; int argument;
        while (source >> address >> operation >> argument)
            sites.push_back({address, operation, argument});
        if (sites.size() != 3909) throw runtime_error("Wrong source census");
        mt19937 random(28301);
        for (const auto& site : sites) {
            for (int assignment = 0; assignment < 3; ++assignment) {
                vector<int> registers(9, 0), spares(assignment + 1, 0);
                if (assignment > 0) {
                    for (int& value : registers) value = random() % 4;
                    for (int& value : spares) value = random() % 4;
                }
                int gap = assignment == 2 ? 3 : 0;
                if (site.operation == "CD") {
                    registers[site.argument] = 0;
                    check_case(site, registers, spares, gap);
                    registers[site.argument] = 1 + assignment;
                    check_case(site, registers, spares, gap);
                } else check_case(site, registers, spares, gap);
            }
        }
        if (case_count != 15252) throw runtime_error("Wrong test-case census");
        set<int> tape;
        int state = 0, head = 0, blank_steps = 0;
        while (blank_steps < 48140 && state != 254) {
            step(state, head, tape);
            ++blank_steps;
        }
        ofstream out(argv[3]); out << "{\"radius\":" << RAD << ",\"contexts\":{"; bool first=true; for(int q=0;q<1000;q++) if(!contexts[q].empty()){ if(!first)out<<",";first=false;out<<"\""<<q<<"\":[";bool fc=true;for(int code:contexts[q]){if(!fc)out<<",";fc=false;out<<code;}out<<"]";}out<<"}}\n";
        cout << "{\"status\":\"PASS\",\"sites\":" << sites.size()
             << ",\"cases\":" << case_count
             << ",\"primitive_literal_steps\":" << primitive_steps
             << ",\"random_seed\":28301,\"assignments_per_branch\":3"
             << ",\"per_case_step_limit\":100000,\"blank_prefix_steps\":" << blank_steps
             << ",\"blank_prefix_halted\":" << (state == 254 ? "true" : "false")
             << ",\"blank_endpoint_state\":" << state
             << ",\"blank_endpoint_head\":" << head
             << ",\"blank_endpoint_one_cells\":" << tape.size() << "}\n";
    } catch (const exception& error) {
        cerr << error.what() << '\n';
        return 1;
    }
}
