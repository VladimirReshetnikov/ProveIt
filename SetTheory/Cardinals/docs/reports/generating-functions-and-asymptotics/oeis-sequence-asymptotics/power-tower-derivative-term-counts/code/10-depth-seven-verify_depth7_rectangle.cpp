// Exact modular certificate for the finite depth-seven A290268 rectangle.
// Standard C++17 only.  Every nonhole integer is certified by a nonzero
// residue modulo at least one listed prime; symmetry holes are checked to be
// zero modulo every prime.  A second, independent jet recurrence is replayed
// modulo the first prime and compared cell by cell.

#include <array>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

namespace {
constexpr int D = 7;
constexpr int K_MAX = 4896; // finite rectangle: 0 <= k <= 4896
constexpr int Q_MAX = 9824; // finite rectangle: 0 <= q <= 9824
constexpr int K_COUNT = K_MAX + 1;
constexpr int Q_COUNT = Q_MAX + 1;
constexpr int INITIAL_COUNT = Q_COUNT + K_MAX;
constexpr std::array<std::uint32_t, 5> PRIMES = {
    1000000007u, 1000000009u, 998244353u, 1004535809u, 469762049u};

using Residues = std::array<std::uint32_t, PRIMES.size()>;

[[noreturn]] void fail(const std::string& message) {
  std::cerr << "FAIL: " << message << '\n';
  std::exit(1);
}

std::uint32_t add_mod(std::uint64_t x, std::uint32_t p) {
  return static_cast<std::uint32_t>(x % p);
}

void mix64(std::uint64_t& h, std::uint64_t x) {
  // FNV-1a-like deterministic transcript fingerprint (diagnostic only).
  for (int i = 0; i < 8; ++i) {
    h ^= static_cast<std::uint8_t>(x & 0xffu);
    h *= 1099511628211ull;
    x >>= 8;
  }
}

} // namespace

int main() {
  std::vector<Residues> row(INITIAL_COUNT), next;

  // k=0 row: [u^7] prod_{ell=0}^{14+q}(14+u-ell).
  for (std::size_t ip = 0; ip < PRIMES.size(); ++ip) {
    const std::uint32_t p = PRIMES[ip];
    std::array<std::uint32_t, D + 1> a{};
    a[0] = 1;
    for (int ell = 0; ell <= 14; ++ell) {
      const std::int64_t c0 = 14 - ell;
      std::array<std::uint32_t, D + 1> b{};
      for (int i = 0; i <= D; ++i) {
        std::uint64_t v = static_cast<std::uint64_t>(a[i]) * c0;
        if (i) v += a[i - 1];
        b[i] = add_mod(v, p);
      }
      a = b;
    }
    row[0][ip] = a[D];
    for (int q = 1; q < INITIAL_COUNT; ++q) {
      const std::uint32_t c0 = p - static_cast<std::uint32_t>(q % p);
      std::array<std::uint32_t, D + 1> b{};
      for (int i = 0; i <= D; ++i) {
        std::uint64_t v = static_cast<std::uint64_t>(a[i]) * c0;
        if (i) v += a[i - 1];
        b[i] = add_mod(v, p);
      }
      a = b;
      row[q][ip] = a[D];
    }
  }

  const std::uint64_t total_cells =
      static_cast<std::uint64_t>(K_COUNT) * Q_COUNT;
  std::vector<std::uint32_t> first_prime_matrix(total_cells);
  std::array<std::uint64_t, PRIMES.size()> first_resolution{};
  std::array<std::uint64_t, PRIMES.size()> zero_residue_counts{};
  std::uint64_t holes = 0;
  std::uint64_t unresolved = 0;
  std::uint64_t transcript = 1469598103934665603ull;
  std::vector<std::pair<int, int>> unresolved_examples;

  int current_count = INITIAL_COUNT;
  for (int k = 0; k <= K_MAX; ++k) {
    if (current_count < Q_COUNT) fail("row became too short");
    for (int q = 0; q <= Q_MAX; ++q) {
      const Residues& r = row[q];
      const std::uint64_t index =
          static_cast<std::uint64_t>(k) * Q_COUNT + q;
      first_prime_matrix[index] = r[0];
      const bool hole = (q == 14) && ((k + D) % 2 == 0);
      bool all_zero = true;
      std::size_t first_nonzero = PRIMES.size();
      for (std::size_t ip = 0; ip < PRIMES.size(); ++ip) {
        if (r[ip] == 0) {
          ++zero_residue_counts[ip];
        } else {
          all_zero = false;
          if (first_nonzero == PRIMES.size()) first_nonzero = ip;
        }
      }
      if (hole) {
        ++holes;
        if (!all_zero) {
          std::ostringstream os;
          os << "symmetry hole is nonzero modulo a prime at k=" << k
             << ", q=" << q;
          fail(os.str());
        }
      } else if (all_zero) {
        ++unresolved;
        if (unresolved_examples.size() < 20)
          unresolved_examples.emplace_back(k, q);
      } else {
        ++first_resolution[first_nonzero];
      }
      mix64(transcript, (static_cast<std::uint64_t>(r[0]) << 1) |
                            static_cast<std::uint64_t>(hole));
    }

    if (k == K_MAX) break;
    next.assign(current_count - 1, Residues{});
    for (int q = 0; q < current_count - 1; ++q) {
      const std::uint64_t coefficient =
          static_cast<std::uint64_t>(k + 2 * D + 2 + q);
      for (std::size_t ip = 0; ip < PRIMES.size(); ++ip) {
        const std::uint32_t p = PRIMES[ip];
        const std::uint64_t v = 2ull * row[q + 1][ip] +
                                coefficient * row[q][ip];
        next[q][ip] = add_mod(v, p);
      }
    }
    row.swap(next);
    --current_count;
  }

  if (unresolved != 0) {
    std::ostringstream os;
    os << unresolved << " nonhole cells vanished modulo every prime";
    if (!unresolved_examples.empty()) {
      os << "; examples:";
      for (const auto& [k, q] : unresolved_examples)
        os << " (" << k << ',' << q << ')';
    }
    fail(os.str());
  }

  // Independent centered-jet recurrence modulo the first prime.
  const std::uint32_t p = PRIMES[0];
  std::array<std::uint32_t, D + 1> base{};
  base[0] = 1;
  for (int ell = 0; ell <= 14; ++ell) {
    const std::int64_t c0 = 14 - ell;
    std::array<std::uint32_t, D + 1> b{};
    for (int i = 0; i <= D; ++i) {
      std::uint64_t v = static_cast<std::uint64_t>(base[i]) * c0;
      if (i) v += base[i - 1];
      b[i] = add_mod(v, p);
    }
    base = b;
  }

  std::uint64_t jet_checked = 0;
  for (int q = 0; q <= Q_MAX; ++q) {
    std::array<std::uint32_t, D + 1> a = base;
    auto check_cell = [&](int k, std::uint32_t value) {
      const std::uint64_t index =
          static_cast<std::uint64_t>(k) * Q_COUNT + q;
      if (first_prime_matrix[index] != value) {
        std::ostringstream os;
        os << "independent recurrence mismatch at k=" << k << ", q=" << q;
        fail(os.str());
      }
      ++jet_checked;
    };
    check_cell(0, a[D]);

    const std::int64_t raw_c0 = 14 - q;
    const std::uint32_t c0 = raw_c0 >= 0
                                 ? static_cast<std::uint32_t>(raw_c0)
                                 : p - static_cast<std::uint32_t>((-raw_c0) % p);
    std::array<std::uint32_t, D + 1> b{};
    for (int i = 0; i <= D; ++i) {
      std::uint64_t v = static_cast<std::uint64_t>(c0) * a[i];
      if (i) v += 2ull * a[i - 1];
      b[i] = add_mod(v, p);
    }
    if (K_MAX >= 1) check_cell(1, b[D]);

    const std::uint64_t r = 2 * D + 1 + q;
    for (int k = 1; k < K_MAX; ++k) {
      const std::uint64_t factor = static_cast<std::uint64_t>(k) * (k + r);
      std::array<std::uint32_t, D + 1> c{};
      for (int i = 0; i <= D; ++i) {
        std::uint64_t v = static_cast<std::uint64_t>(c0) * b[i] +
                          factor * a[i];
        if (i) v += 2ull * b[i - 1];
        c[i] = add_mod(v, p);
      }
      check_cell(k + 1, c[D]);
      a = b;
      b = c;
    }

    // Advance V_0 for q -> q+1 by multiplication by u-(q+1).
    if (q < Q_MAX) {
      const std::uint32_t neg = p - static_cast<std::uint32_t>((q + 1) % p);
      std::array<std::uint32_t, D + 1> newer{};
      for (int i = 0; i <= D; ++i) {
        std::uint64_t v = static_cast<std::uint64_t>(neg) * base[i];
        if (i) v += base[i - 1];
        newer[i] = add_mod(v, p);
      }
      base = newer;
    }
  }

  if (jet_checked != total_cells) fail("independent replay cell count mismatch");

  std::cout << "{\n";
  std::cout << "  \"depth\": 7,\n";
  std::cout << "  \"k_range\": [0, " << K_MAX << "],\n";
  std::cout << "  \"q_range\": [0, " << Q_MAX << "],\n";
  std::cout << "  \"cells\": " << total_cells << ",\n";
  std::cout << "  \"symmetry_holes\": " << holes << ",\n";
  std::cout << "  \"unresolved_nonholes\": " << unresolved << ",\n";
  std::cout << "  \"largest_derivative_order\": "
            << (2 * K_MAX + 2 * D + 1 + Q_MAX) << ",\n";
  std::cout << "  \"primes\": [";
  for (std::size_t i = 0; i < PRIMES.size(); ++i) {
    if (i) std::cout << ", ";
    std::cout << PRIMES[i];
  }
  std::cout << "],\n";
  std::cout << "  \"first_resolution_counts\": [";
  for (std::size_t i = 0; i < PRIMES.size(); ++i) {
    if (i) std::cout << ", ";
    std::cout << first_resolution[i];
  }
  std::cout << "],\n";
  std::cout << "  \"zero_residue_counts\": [";
  for (std::size_t i = 0; i < PRIMES.size(); ++i) {
    if (i) std::cout << ", ";
    std::cout << zero_residue_counts[i];
  }
  std::cout << "],\n";
  std::cout << "  \"independent_jet_cells_checked\": " << jet_checked << ",\n";
  std::cout << "  \"transcript_fingerprint_fnv64\": \"0x" << std::hex
            << std::setw(16) << std::setfill('0') << transcript << std::dec
            << "\",\n";
  std::cout << "  \"status\": \"PASS\"\n";
  std::cout << "}\n";
  return 0;
}
