// Exact literal finite tests for all direct state-identification candidates.
// A cutoff is reported as a cutoff, never as a semantic counterexample.
#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <stdexcept>
using namespace std;
struct Row { int write, move, next; };
struct Fixture { int state, head, target_state, target_head; array<unsigned char,4096> tape{}, target{}; array<int,9> values{}; };
struct Outcome { int status, steps; bool wrong_boundary; };
Row table[256][2];
vector<int> states, by_state[256];
vector<Fixture> fixtures;
const char* names[4] = {"passed_finite_test", "tape_bound", "unexpected_halt", "fuel_bound"};

bool same_frame(const array<unsigned char,4096>& one, const Fixture& c, int head) {
    if (head<1 || head+40>=4096 || !one[head-1]) return false;
    for (int p=0;p<head-1;p++) if (one[p]) return false;
    for (int p=0;p<40;p++) if (one[head+p] != c.target[c.target_head+p]) return false;
    int p=head+40; while(p<4096 && !one[p]) p++; if(p>=4096) return false; p++;
    int n=0;
    while(p<4095) {
        if(one[p]) return false;
        if(!one[p+1]) { for(int j=p+1;j<4096;j++) if(one[j]) return false; return n>=10; }
        int k=p+1; while(k<4096 && one[k]) k++;
        if(n<9 && c.values[n] != k-p-2) return false;
        n++; p=k;
    }
    return false;
}

Outcome run(int source, int destination, const Fixture& c, int fuel) {
    auto tape = c.tape;
    int state = c.state == source ? destination : c.state, head = c.head;
    bool wrong = false;
    for (int step = 0; step < fuel; ++step) {
        if (head < 0 || head >= 4096) return {1,step,wrong};
        Row row = table[state][tape[head]];
        tape[head] = row.write;
        head += row.move;
        state = row.next == source ? destination : row.next;
        if (state == 254) return {c.target_state == 254 ? 0 : 2,step+1,wrong};
        if (state == c.target_state) {
            if (same_frame(tape,c,head)) return {0,step+1,wrong};
            wrong = true;
        }
    }
    return {3,fuel,wrong};
}

int main(int argc, char** argv) {
    if (argc < 7) {
        cerr << "Usage: directed_folds TABLE FIXTURES FUEL micro|full DECISIONS.csv CANDIDATES|all\n";
        return 2;
    }
    const bool full = string(argv[4]) == "full";
    ifstream input_table(argv[1]);
    if (!input_table) throw runtime_error("Cannot open table");
    string line;
    while (getline(input_table,line)) {
        if (line.empty() || line[0] == '#') continue;
        int q,b,w,t; char d;
        if (sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&t) != 5) throw runtime_error("Bad row");
        table[q][b] = {w,d == 'R' ? 1 : -1,t};
        if (b == 0) states.push_back(q);
    }
    ifstream input_cases(argv[2]);
    int count; input_cases >> count;
    if (!input_cases || count < 0) throw runtime_error("Bad fixture header");
    fixtures.reserve(count);
    for (int i = 0; i < count; ++i) {
        Fixture c; int length,position;
        input_cases >> c.state >> c.head >> length; c.head += 1024;
        while (length--) { input_cases >> position; c.tape.at(position+1024)=1; }
        input_cases >> c.target_state >> c.target_head >> length; c.target_head += 1024;
        while (length--) { input_cases >> position; c.target.at(position+1024)=1; }
        if (c.target_state != 254) {
            int p=c.target_head+40; while(p<4096 && !c.target[p]) p++;
            if(p>=4096) throw runtime_error("Missing header"); p++;
            for(int j=0;j<9;j++) { int k=p+1; while(k<4096 && c.target[k]) k++;
                c.values[j]=k-p-2; p=k; }
        }
        fixtures.push_back(c);
        if (full) {
            input_cases >> length;
            while (length--) { input_cases >> position; by_state[position].push_back(i); }
        } else by_state[c.state].push_back(i);
        if (!input_cases) throw runtime_error("Truncated fixture");
    }
    vector<pair<int,int>> pairs;
    if (string(argv[6]) == "all") {
        for (int q : states) for (int r : states) if (q != r) pairs.emplace_back(q,r);
    } else {
        ifstream candidate_input(argv[6]); string tag; int q,r;
        while (candidate_input >> tag >> q >> r) {
            if (tag != "PASS") throw runtime_error("Bad candidate line");
            pairs.emplace_back(q,r);
        }
    }
    ofstream decisions(argv[5]);
    decisions << "source,destination,status,fixture,steps,wrong_expected_boundary_seen\n";
    long totals[4]{}, wrong_counts[4]{};
    const int fuel = stoi(argv[3]);
    for (auto [source,destination] : pairs) {
        Outcome outcome{0,0,false}; int failed_fixture = -1;
        for (int i : by_state[source]) {
            outcome = run(source,destination,fixtures[i],fuel);
            if (outcome.status) { failed_fixture = i; break; }
        }
        totals[outcome.status]++;
        if (outcome.wrong_boundary) wrong_counts[outcome.status]++;
        decisions << source << ',' << destination << ',' << names[outcome.status] << ','
                  << failed_fixture << ',' << outcome.steps << ',' << outcome.wrong_boundary << '\n';
        if (!outcome.status) cout << "PASS " << source << ' ' << destination << '\n';
    }
    string summary_path = string(argv[5]) + ".summary.json";
    ofstream summary(summary_path);
    summary << "{\n  \"scope\": \"finite semantic-frame folds, variable head and gap and spares; cutoffs are inconclusive\",\n"
            << "  \"mode\": \"" << (full ? "whole instruction" : "first occurrence micro context") << "\",\n"
            << "  \"candidates\": " << pairs.size() << ",\n  \"fixtures\": " << fixtures.size()
            << ",\n  \"fuel_per_fixture\": " << fuel << ",\n  \"tape_coordinates\": [-1024, 3071],\n"
            << "  \"outcomes\": {\n";
    for (int i=0;i<4;i++) summary << "    \"" << names[i] << "\": " << totals[i] << (i<3 ? "," : "") << '\n';
    summary << "  },\n  \"observed_wrong_expected_boundaries_by_outcome\": [";
    for (int i=0;i<4;i++) summary << wrong_counts[i] << (i<3 ? ", " : "");
    summary << "]\n}\n";
    cerr << "Candidates " << pairs.size() << "; passes " << totals[0] << "; tape cutoffs "
         << totals[1] << "; unexpected halts " << totals[2] << "; fuel cutoffs " << totals[3] << '\n';
}
