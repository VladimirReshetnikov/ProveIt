// Independent exact breadth-first search of coloring orbits.
// C++17, no dependencies. Input is code/bfs_cases.txt; output is CSV.
// A coloring c is encoded by sum_i c[i]*k^i. No theorem is used by this BFS.
#include <algorithm>
#include <cstdint>
#include <exception>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

int main() {
    try {
        std::cout << "case,n,k,expected,observed,match,orbit_sum,orbit_xor\n";
        std::string label;
        std::uint32_t n, k, letters;
        std::uint64_t expected;
        while (std::cin >> label >> n >> k >> letters >> expected) {
            if (n == 0 || k < 2 || letters == 0 || n > 1000)
                throw std::runtime_error("Invalid dimensions.");
            std::vector<std::uint64_t> powers(n + 1, 1);
            for (std::uint32_t i = 1; i <= n; ++i) {
                powers[i] = powers[i-1] * k;
                if (powers[i] > 200000000ULL)
                    throw std::runtime_error("Universe exceeds the deliberate safety limit.");
            }
            std::vector<std::vector<std::uint64_t>> weights(
                letters, std::vector<std::uint64_t>(n, 0));
            for (std::uint32_t a = 0; a < letters; ++a)
                for (std::uint32_t q = 0; q < n; ++q) {
                    std::uint32_t image;
                    if (!(std::cin >> image) || image >= n)
                        throw std::runtime_error("Invalid transformation.");
                    weights[a][image] += powers[q];
                }
            std::uint64_t initial = 0;
            for (std::uint32_t q = 0; q < n; ++q) {
                std::uint32_t color;
                if (!(std::cin >> color) || color >= k)
                    throw std::runtime_error("Invalid coloring.");
                initial += color * powers[q];
            }
            std::vector<std::uint8_t> seen(powers[n], 0);
            std::vector<std::uint32_t> queue;
            queue.reserve(powers[n]);
            queue.push_back(static_cast<std::uint32_t>(initial));
            seen[initial] = 1;
            std::vector<std::uint32_t> digits(n, 0);
            for (std::size_t head = 0; head < queue.size(); ++head) {
                auto code = queue[head];
                for (std::uint32_t i = 0; i < n; ++i) {
                    digits[i] = code % k;
                    code /= k;
                }
                for (const auto& weight : weights) {
                    std::uint64_t next = 0;
                    for (std::uint32_t i = 0; i < n; ++i)
                        next += digits[i] * weight[i];
                    if (!seen[next]) {
                        seen[next] = 1;
                        queue.push_back(static_cast<std::uint32_t>(next));
                    }
                }
            }
            std::uint64_t sum = 0, bitxor = 0;
            for (auto code : queue) { sum += code; bitxor ^= code; }
            const bool match = queue.size() == expected;
            std::cout << label << ',' << n << ',' << k << ',' << expected << ','
                      << queue.size() << ',' << match << ',' << sum << ',' << bitxor << '\n';
            if (!match) return 2;
        }
        if (!std::cin.eof()) throw std::runtime_error("Malformed input.");
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "orbit_count: " << e.what() << '\n';
        return 1;
    }
}
