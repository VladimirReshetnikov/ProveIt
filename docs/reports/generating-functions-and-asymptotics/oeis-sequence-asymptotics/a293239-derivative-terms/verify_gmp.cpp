// Exact verification of OEIS A293239 via Lehmer--Comtet coefficients.
// Build: c++ -O3 -std=c++17 verify_gmp.cpp -lgmpxx -lgmp -o verify_gmp
// Run: ./verify_gmp 3000 data
// This finite computation does not prove the conjecture for all n.
#include <gmpxx.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

static std::uint64_t candidate(std::uint64_t n) {
    if (n == 0) return 1;
    return 1 + n*(n+1)/2 - (n-1)/4 - (n >= 8 ? 1 : 0);
}
static bool known_zero(long m, long r) {
    return (m == 8 && r == 5) || (m >= 5 && m % 4 == 1 && r == (m-1)/2);
}
int main(int argc, char **argv) {
  try {
    long N = 3000;
    if (argc > 1) {
      std::size_t consumed = 0;
      const std::string arg = argv[1];
      N = std::stol(arg, &consumed);
      if (consumed != arg.size()) throw std::invalid_argument("invalid bound");
    }
    if (N < 1 || N > 100000) throw std::invalid_argument("N must be in [1,100000]");
    const std::filesystem::path out = argc > 2 ? argv[2] : "data";
    std::filesystem::create_directories(out);
    std::ofstream counts(out / "counts.csv"), zeros(out / "zeros.csv");
    if (!counts || !zeros) throw std::runtime_error("cannot create output files");
    counts << "n,actual_count,candidate_count,row_nonzero,row_zeros,cumulative_unexpected\n";
    zeros << "m,r,classification\n";
    counts << "0,1,1,1,0,0\n1,2,2,1,0,0\n";
    std::vector<mpz_class> pp(1), prev(2);
    pp[0] = 1; prev[1] = 1;
    std::uint64_t total = 2, zero_total = 0, extra = 0;
    std::uint64_t count_mismatches = 0, missing_known = 0;
    for (long m = 2; m <= N; ++m) {
      std::vector<mpz_class> cur(static_cast<std::size_t>(m+1));
      std::uint64_t row_zeros = 0;
      for (long r = 1; r <= m; ++r) {
        cur[r] = prev[r-1];
        if (r < m) cur[r] += (r-m+1)*prev[r] + (m-1)*pp[r-1];
        const bool is_zero = cur[r] == 0;
        const bool expected = known_zero(m,r);
        if (is_zero) {
          ++row_zeros; ++zero_total;
          if (!expected) ++extra;
          zeros << m << ',' << r << ','
                << (m==8 && r==5 ? "exceptional" : expected ? "symmetry" : "UNEXPECTED") << '\n';
        } else if (expected) ++missing_known;
      }
      total += static_cast<std::uint64_t>(m)-row_zeros;
      if (total != candidate(m)) ++count_mismatches;
      counts << m << ',' << total << ',' << candidate(m) << ','
             << m-row_zeros << ',' << row_zeros << ',' << extra << '\n';
      pp.swap(prev); prev.swap(cur);
    }
    const std::uint64_t tested = static_cast<std::uint64_t>(N)*(N+1)/2;
    std::ofstream report(out / "gmp_report.txt");
    if (!report) throw std::runtime_error("cannot create report");
    report << "Exact signed-integer recurrence verification\n"
           << "GMP version: " << gmp_version << "\n"
           << "Maximum row: " << N << "\n"
           << "Triangle entries tested (1 <= r <= m <= N): " << tested << "\n"
           << "Zero entries: " << zero_total << "\n"
           << "Unexpected zero entries: " << extra << "\n"
           << "Missing symmetry/exceptional zeros: " << missing_known << "\n"
           << "Count mismatches: " << count_mismatches << "\n"
           << "a(N): " << total << "\n"
           << "candidate(N): " << candidate(N) << "\n"
           << "Scope: finite verification only; no all-n proof is claimed.\n";
    report.close(); counts.close(); zeros.close();
    if (!counts || !zeros || !report) throw std::runtime_error("output write failed");
    std::cout << "N=" << N << "; tested=" << tested << "; zeros=" << zero_total
              << "; unexpected=" << extra << "; a(N)=" << total << '\n';
    return extra || missing_known || count_mismatches ? 1 : 0;
  } catch (const std::exception &e) {
    std::cerr << "Error: " << e.what() << '\n'; return 2;
  }
}
