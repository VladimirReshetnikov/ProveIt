// Exhaustive, solver-independent certificate verifier. Requires C++20.
#include "core_enumeration.hpp"
#include <fstream>
#include <cctype>
#include <iostream>
#include <map>
#include <sstream>
#include <string>

using shuffleproof::U;
using Key = std::pair<unsigned, U>;

static void require(bool condition, const std::string &message) {
    if (!condition) throw std::runtime_error(message);
}

int main(int argc, char **argv) {
    try {
        const std::string path = argc > 1 ? argv[1] : "certificates/cores.cert";
        std::ifstream file(path);
        require(bool(file), "cannot open certificate file: " + path);
        std::map<unsigned, std::set<U>> supplied;
        std::size_t count = 0, lineno = 0;
        unsigned min_drop = 1000, max_drop = 0;
        std::string line;
        while (std::getline(file, line)) {
            ++lineno;
            if (line.empty() || line[0] == '#') continue;
            const std::string loc = "line " + std::to_string(lineno) + ": ";
            for (unsigned char ch : line)
                require(std::isdigit(ch) || std::isspace(ch),
                        loc + "only nonnegative decimal integers are allowed");
            std::istringstream input(line);
            unsigned m, n;
            U family;
            require(bool(input >> m >> n >> family), loc + "invalid header");
            require(2 <= m && m <= 6 && m <= n && n <= 20, loc + "dimensions");
            require(m == 6 || (family >> (1U << m)) == 0, loc + "family out of range");
            std::vector<unsigned> f(m), g(n), t(n), s, image(n, 0);
            for (auto &x : f) require(bool(input >> x) && x < m, loc + "row map");
            for (auto &x : g) require(bool(input >> x) && x < n, loc + "column map");
            for (auto &x : t)
                require(bool(input >> x) && 0 < x && x < (1U << m), loc + "source mask");
            std::string extra;
            require(!(input >> extra), loc + "trailing data");
            auto sorted_f = f;
            std::sort(sorted_f.begin(), sorted_f.end());
            for (unsigned i = 0; i < m; ++i)
                require(sorted_f[i] == i, loc + "row map is not a permutation");
            for (U z = family; z; z &= z - 1)
                s.push_back(std::countr_zero(z));
            require(s.size() == n, loc + "wrong number of target columns");
            unsigned source_rows = 0, size_s = 0, size_t = 0;
            for (unsigned j = 0; j < n; ++j) {
                source_rows |= t[j];
                size_s += std::popcount(s[j]);
                size_t += std::popcount(t[j]);
                for (unsigned i = 0; i < m; ++i)
                    if ((t[j] >> i) & 1U) image[j] |= 1U << f[i];
                image[g[j]] |= t[j];
            }
            require(source_rows == (1U << m) - 1, loc + "empty source row");
            require(size_t < size_s, loc + "source is not strictly smaller");
            require(image == s, loc + "transition image is not the target");
            require(supplied[m].insert(family).second, loc + "duplicate target");
            min_drop = std::min(min_drop, size_s - size_t);
            max_drop = std::max(max_drop, size_s - size_t);
            ++count;
        }
        require(!file.bad(), "input read error");
        for (unsigned m = 2; m <= 6; ++m) {
            shuffleproof::Enumeration enumeration(m);
            enumeration.run();
            require(enumeration.representatives == supplied[m],
                    "exhaustive coverage failed at m=" + std::to_string(m));
            std::cout << "m=" << m << ": antichains=" << enumeration.total()
                      << ", canonical cores=" << enumeration.representatives.size()
                      << ", exact certificate coverage: PASS\n";
        }
        std::cout << "Certificates checked: " << count << "\n"
                  << "Cardinality decrease: " << min_drop << " through " << max_drop << "\n"
                  << "Full support, strict decrease, exact image, row permutations: PASS\n"
                  << "OVERALL: PASS\n";
    } catch (const std::exception &error) {
        std::cerr << "FAIL: " << error.what() << '\n';
        return 1;
    }
}
