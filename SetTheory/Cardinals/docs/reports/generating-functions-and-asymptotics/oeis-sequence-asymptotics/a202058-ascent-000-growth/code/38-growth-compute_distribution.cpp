// Normalized floating compact-state transfer for diagnostic purposes only.
// No interval error bound is asserted. Tiny groups can have large future effects.
// Compile: g++ -O3 -std=c++17 compute_distribution.cpp -o compute_distribution
// Run twice: ./compute_distribution 1200 1e-120, and again with 1e-200.
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <vector>

struct Group { std::vector<long double> last; };

int main(int argc, char** argv) {
    const int max_n = argc > 1 ? std::atoi(argv[1]) : 600;
    const long double cutoff = argc > 2 ? std::strtold(argv[2], nullptr) : 1e-120L;
    if (max_n < 1 || cutoff < 0) return 1;
    using Layer = std::vector<std::vector<Group>>;
    Layer current(max_n + 3, std::vector<Group>(max_n / 2 + 4));
    Layer next = current;
    current[1][1].last = {0, 1};
    long double log_count = 0;
    // Columns: n, log(c_n), c_n/(n*c_(n-1)), mean(m), mean(h).
    std::cout << std::setprecision(20) << "1 0 1 1 1\n";

    for (int n = 1; n < max_n; ++n) {
        for (int m = n % 2; m <= n; m += 2) {
            for (int h = 1; h <= (n - m) / 2 + 1; ++h) {
                auto& probabilities = current[m][h].last;
                if (probabilities.empty()) continue;
                long double total = 0;
                for (auto value : probabilities) total += value;
                if (total < cutoff) {
                    std::vector<long double>().swap(probabilities);
                    continue;
                }
                auto destination = [&](int new_m, int new_h)
                    -> std::vector<long double>& {
                    auto& result = next[new_m][new_h].last;
                    if (result.empty()) result.resize(new_m + new_h, 0);
                    return result;
                };
                std::vector<long double>* repeat = nullptr;
                std::vector<long double>* repeat_ascent = nullptr;
                if (m > 0) {
                    repeat = &destination(m - 1, h);
                    repeat_ascent = &destination(m - 1, h + 1);
                }
                auto& new_ascent = destination(m + 1, h);
                std::vector<long double>* new_nonascent = nullptr;
                if (h > 1) new_nonascent = &destination(m + 1, h - 1);

                // Compute tails directly rather than subtracting nearly equal sums.
                std::vector<long double> suffix(m + h + 1, 0);
                for (int j = m + h - 1; j >= 0; --j)
                    suffix[j] = suffix[j + 1] + probabilities[j];
                long double prefix = 0;
                for (int i = 0; i < m + h; ++i) {
                    prefix += probabilities[i];
                    const long double tail = suffix[i + 1];
                    if (i < m) {
                        (*repeat)[i] += tail;
                        (*repeat_ascent)[i] += prefix;
                    } else {
                        new_ascent[i + 1] += prefix;
                        if (new_nonascent && i + 1 < int(new_nonascent->size()))
                            (*new_nonascent)[i + 1] += tail;
                    }
                }
                std::vector<long double>().swap(probabilities);
            }
        }
        long double total = 0, mean_m = 0, mean_h = 0;
        for (int m = (n + 1) % 2; m <= n + 1; m += 2)
            for (int h = 1; h <= (n + 1 - m) / 2 + 1; ++h)
                for (auto value : next[m][h].last) {
                    total += value;
                    mean_m += m * value;
                    mean_h += h * value;
                }
        for (int m = (n + 1) % 2; m <= n + 1; m += 2)
            for (int h = 1; h <= (n + 1 - m) / 2 + 1; ++h)
                for (auto& value : next[m][h].last) value /= total;
        current.swap(next);
        log_count += std::log(total);
        std::cout << n + 1 << ' ' << log_count << ' ' << total / (n + 1)
                  << ' ' << mean_m / total << ' ' << mean_h / total << std::endl;
    }
}
