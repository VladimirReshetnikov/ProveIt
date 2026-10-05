// Exact positive compact-state transfer for OEIS A202058.
// Compile: g++ -O3 -std=c++17 compute_exact.cpp -lgmpxx -lgmp -o compute_exact
// Run: ./compute_exact 395 > exact_coefficients_395.txt
#include <cstdlib>
#include <iostream>
#include <vector>
#include <gmpxx.h>

using Integer = mpz_class;
struct Group { std::vector<Integer> last; };

int main(int argc, char** argv) {
    const int max_n = argc > 1 ? std::atoi(argv[1]) : 176;
    if (max_n < 1) return 1;
    using Layer = std::vector<std::vector<Group>>;
    Layer current(max_n + 3, std::vector<Group>(max_n / 2 + 4));
    Layer next = current;
    current[1][1].last = {0, 1};  // Initial zero: (m,h,L)=(1,1,1).
    std::cout << "0 1\n1 1\n";

    for (int n = 1; n < max_n; ++n) {
        // At level n, m has the parity of n and h <= (n-m)/2+1.
        for (int m = n % 2; m <= n; m += 2) {
            for (int h = 1; h <= (n - m) / 2 + 1; ++h) {
                auto& counts = current[m][h].last;
                if (counts.empty()) continue;
                Integer total = 0;
                for (const auto& value : counts) total += value;
                if (total == 0) {
                    std::vector<Integer>().swap(counts);
                    continue;
                }
                auto destination = [&](int new_m, int new_h)
                    -> std::vector<Integer>& {
                    auto& result = next[new_m][new_h].last;
                    if (result.empty()) result.resize(new_m + new_h);
                    return result;
                };
                std::vector<Integer>* repeat = nullptr;
                std::vector<Integer>* repeat_ascent = nullptr;
                if (m > 0) {
                    repeat = &destination(m - 1, h);
                    repeat_ascent = &destination(m - 1, h + 1);
                }
                auto& new_ascent = destination(m + 1, h);
                std::vector<Integer>* new_nonascent = nullptr;
                if (h > 1) new_nonascent = &destination(m + 1, h - 1);

                // Prefix sums over old L count the condition i >= L.
                Integer prefix = 0;
                for (int i = 0; i < m + h; ++i) {
                    prefix += counts[i];
                    const Integer suffix = total - prefix;
                    if (i < m) {
                        (*repeat)[i] += suffix;
                        (*repeat_ascent)[i] += prefix;
                    } else {
                        new_ascent[i + 1] += prefix;
                        if (new_nonascent && i + 1 < int(new_nonascent->size()))
                            (*new_nonascent)[i + 1] += suffix;
                    }
                }
                std::vector<Integer>().swap(counts);
            }
        }
        Integer answer = 0;
        for (int m = (n + 1) % 2; m <= n + 1; m += 2)
            for (int h = 1; h <= (n + 1 - m) / 2 + 1; ++h)
                for (const auto& value : next[m][h].last) answer += value;
        current.swap(next);
        std::cout << n + 1 << ' ' << answer << std::endl;
    }
}
