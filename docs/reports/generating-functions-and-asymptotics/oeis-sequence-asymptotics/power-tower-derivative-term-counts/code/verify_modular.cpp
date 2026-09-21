// A290268: exact recurrence over Z/modulus Z. C++17, standard library only.
// Usage: verify_modular MAX_N MODULUS OUTPUT_PREFIX [WATCH_CSV]
// A nonzero residue certifies a nonzero integer coefficient. A zero residue
// alone does NOT certify an integer zero. See combine_certificates.py.
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

struct Watch { int n, k, j; };

bool forced_zero(int n, int k, int j) {
    return (j == k && n > 2 * k)
        || (k % 2 == 0 && n == 4 * k - 2 * j + 1);
}

long long upper_bound(int n) {
    if (n % 2 == 0) return (1LL * n * n + 2LL * n + 2) / 2;
    return (1LL * n * n + 2LL * n + 1) / 2 - (n + 1) / 8;
}

int main(int argc, char** argv) {
    try {
        if (argc < 4 || argc > 5)
            throw std::runtime_error("Usage: verify_modular N MOD PREFIX [WATCH_CSV]");
        const int N = std::stoi(argv[1]);
        const std::int64_t mod = std::stoll(argv[2]);
        const std::string prefix = argv[3];
        // These bounds also make every intermediate safely fit int64_t.
        if (N < 0 || N > 10000 || mod < 2 || mod > 2000000000LL)
            throw std::runtime_error("Require 0 <= N <= 10000 and 2 <= MOD <= 2000000000.");
        std::vector<Watch> watches;
        if (argc == 5) {
            std::ifstream in(argv[4]);
            if (!in) throw std::runtime_error("Cannot read watch file.");
            std::string line;
            std::getline(in, line); // header n,k,j
            while (std::getline(in, line)) {
                if (line.empty()) continue;
                for (char& c : line) if (c == ',') c = ' ';
                std::istringstream ss(line);
                Watch w{};
                if (!(ss >> w.n >> w.k >> w.j) || w.n < 1 || w.n > N
                    || w.k < 1 || w.k > w.n || w.j < 0 || w.j > w.k)
                    throw std::runtime_error("Invalid watch coordinate.");
                watches.push_back(w);
            }
        }
        std::ofstream zeros(prefix + "_zeros.csv");
        std::ofstream counts(prefix + "_counts.csv");
        std::ofstream residues(prefix + "_watches.csv");
        if (!zeros || !counts || !residues)
            throw std::runtime_error("Cannot create output files.");
        zeros << "n,k,j\n";
        counts << "n,modulus,potential_cells,forced_zero_cells,extra_modular_zeros,nonzero_residues\n";
        residues << "n,k,j,modulus,residue\n";
        const std::size_t stride = static_cast<std::size_t>(N) + 3;
        std::vector<std::uint32_t> a(stride * stride, 0), b(a.size(), 0);
        a[0] = 1;
        std::uint64_t total_cells = 0, extra_zeros = 0;
        for (int n = 0; n <= N; ++n) {
            std::uint64_t forced = 0, extras = 0, nonzeros = n == 0 ? 1 : 0;
            for (int k = 1; k <= n; ++k) {
                for (int j = 0; j <= k; ++j) {
                    const auto residue = a[static_cast<std::size_t>(k) * stride + j];
                    const bool expected = forced_zero(n, k, j);
                    if (expected) {
                        ++forced;
                        if (residue != 0)
                            throw std::runtime_error("A mathematically forced zero has a nonzero residue.");
                    } else if (residue == 0) {
                        ++extras;
                        zeros << n << ',' << k << ',' << j << '\n';
                    }
                    if (residue != 0) ++nonzeros;
                }
            }
            const auto cells = n == 0 ? 1ULL : 1ULL * n * (n + 3) / 2;
            if (cells - forced != static_cast<std::uint64_t>(upper_bound(n))
                || nonzeros + extras + forced != cells)
                throw std::runtime_error("Support-count consistency check failed.");
            counts << n << ',' << mod << ',' << cells << ',' << forced << ','
                   << extras << ',' << nonzeros << '\n';
            total_cells += cells;
            extra_zeros += extras;
            for (const auto& w : watches) if (w.n == n)
                residues << n << ',' << w.k << ',' << w.j << ',' << mod << ','
                         << a[static_cast<std::size_t>(w.k) * stride + w.j] << '\n';
            if (n % 500 == 0) std::cout << "checked n=" << n << '\n';
            if (n == N) break;
            // Gather recurrence. Entries outside the previous triangle remain zero;
            // every entry in the enlarged new triangle is overwritten before swapping.
            for (int k = 0; k <= n + 1; ++k) {
                for (int j = 0; j <= k; ++j) {
                    const std::size_t ix = static_cast<std::size_t>(k) * stride + j;
                    std::int64_t value = (2LL * k - n) * a[ix]
                                      + (1LL * j + 1) * a[ix + 1];
                    if (k != 0) {
                        value += a[ix - stride];
                        if (j != 0) value += 2LL * a[ix - stride - 1];
                    }
                    value %= mod;
                    if (value < 0) value += mod;
                    b[ix] = static_cast<std::uint32_t>(value);
                }
            }
            a.swap(b);
        }
        std::cout << "max_n=" << N << " modulus=" << mod
                  << " total_cells=" << total_cells
                  << " extra_modular_zeros=" << extra_zeros << '\n';
        std::ofstream summary(prefix + "_summary.txt");
        summary << "max_n=" << N << "\nmodulus=" << mod
                << "\ntotal_cells=" << total_cells
                << "\nextra_modular_zeros=" << extra_zeros
                << "\nforced_zero_check=PASS\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
}
