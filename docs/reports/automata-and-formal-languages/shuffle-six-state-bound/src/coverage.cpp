// Independent, exhaustive coverage check for shuffle predecessor certificates.
// C++17; no SAT/SMT library, and no canonicalization from the search enumerator.
// Input: TSV exported by check_certificates.py, columns (m, family mask).
// Build: c++ -O3 -std=c++17 src/coverage.cpp -o audit/coverage
// Run:   audit/coverage audit/verified_targets.tsv > audit/coverage.json
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using U = std::uint64_t;

class Checker {
    int m;
    int limit;
    std::array<U, 64> conflicts{};
    std::vector<U> orbit;
    std::array<U, 64> hard_by_columns{};
    U visited = 0, hard_count = 0;

    static int bit_index(U x) { return __builtin_ctzll(x); }

    // This predicate is written independently of the search canonicalizer.
    bool hard(U family) const {
        std::array<U, 6> row_masks{};
        int j = 0;
        for (int s = 1; s < limit - 1; ++s) {
            if (!(family & (U(1) << s))) continue;
            if (__builtin_popcount(unsigned(s)) < 2) return false;
            for (int i = 0; i < m; ++i)
                if (s & (1 << i)) row_masks[i] |= U(1) << j;
            ++j;
        }
        for (int i = 0; i < m; ++i) {
            if (__builtin_popcountll(row_masks[i]) < 2) return false;
            for (int k = 0; k < m; ++k) {
                if (i != k && (row_masks[i] | row_masks[k]) == row_masks[k])
                    return false;
            }
        }
        return true;
    }

    // Candidates are precisely the larger masks incomparable with all members.
    // Deleting the lowest candidate before descent enforces increasing order.
    void visit(U family, U candidates, unsigned depth) {
        ++visited;
        if (hard(family)) {
            ++hard_count;
            ++hard_by_columns[depth];
            if (!std::binary_search(orbit.begin(), orbit.end(), family)) {
                throw std::runtime_error("UNCOVERED family: m=" + std::to_string(m)
                                         + " mask=" + std::to_string(family));
            }
        }
        while (candidates) {
            int s = bit_index(candidates);
            candidates &= candidates - 1;
            visit(family | (U(1) << s), candidates & ~conflicts[s], depth + 1);
        }
    }

public:
    explicit Checker(int rows): m(rows), limit(1 << rows) {
        for (int s = 1; s < limit - 1; ++s)
            for (int t = 1; t < limit - 1; ++t)
                if ((s | t) == s || (s | t) == t)
                    conflicts[s] |= U(1) << t;
    }

    void run(const std::vector<U>& representatives) {
        std::vector<int> p;
        for (int i = 0; i < m; ++i) p.push_back(i);
        do {
            std::array<int, 64> image{};
            for (int s = 1; s < limit - 1; ++s)
                for (int i = 0; i < m; ++i)
                    if (s & (1 << i)) image[s] |= 1 << p[i];
            for (U family: representatives) {
                U renamed = 0;
                for (int s = 1; s < limit - 1; ++s)
                    if (family & (U(1) << s)) renamed |= U(1) << image[s];
                orbit.push_back(renamed);
            }
        } while (std::next_permutation(p.begin(), p.end()));
        std::sort(orbit.begin(), orbit.end());
        orbit.erase(std::unique(orbit.begin(), orbit.end()), orbit.end());
        U all = 0;
        for (int s = 1; s < limit - 1; ++s) all |= U(1) << s;
        visit(0, all, 0);
        if (hard_count != orbit.size())
            throw std::runtime_error("orbit contains non-hard family or invalid input");
        std::cout << "    {\"m\":" << m << ",\"representatives\":" << representatives.size()
                  << ",\"labeled_antichains_visited\":" << visited
                  << ",\"hard_labeled_families\":" << hard_count
                  << ",\"orbit_size\":" << orbit.size() << ",\"by_columns\":{";
        bool first = true;
        for (unsigned j = 0; j < hard_by_columns.size(); ++j) {
            if (!hard_by_columns[j]) continue;
            if (!first) std::cout << ',';
            first = false;
            std::cout << '\"' << j << "\":" << hard_by_columns[j];
        }
        std::cout << "}}";
    }
};

int main(int argc, char** argv) {
    try {
        if (argc != 2) throw std::runtime_error("usage: coverage verified_targets.tsv");
        std::ifstream in(argv[1]);
        if (!in) throw std::runtime_error("cannot open target file");
        std::array<std::vector<U>, 7> targets;
        int m; U family;
        while (in >> m >> family) {
            if (m < 2 || m > 6) throw std::runtime_error("m outside 2..6");
            U allowed = 0;
            for (int s = 1; s < (1 << m) - 1; ++s) allowed |= U(1) << s;
            if (family & ~allowed) throw std::runtime_error("invalid family bit");
            targets[m].push_back(family);
        }
        if (!in.eof()) throw std::runtime_error("malformed TSV");
        std::cout << "{\n  \"coverage\": [\n";
        for (int rows = 2; rows <= 6; ++rows) {
            Checker checker(rows);
            checker.run(targets[rows]);
            std::cout << (rows == 6 ? "\n" : ",\n");
        }
        std::cout << "  ],\n  \"result\": \"PASS: every hard family has a checked representative\"\n}\n";
    } catch (const std::exception& error) {
        std::cerr << "FAIL: " << error.what() << '\n';
        return 1;
    }
    return 0;
}
