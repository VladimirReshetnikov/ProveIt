// Exhaust the strict cubic witness condition on 253507 < p <= HIGH.
// Build with g++ -O3 -std=c++17 -fopenmp cubic_tail.cpp -o cubic_tail.
// OpenMP only parallelizes independent residue classes. With no -fopenmp the
// same source runs serially. All integer operations are exact.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>

using Int = std::int64_t;
using Word = std::uint64_t;
using Wide = __int128_t;
constexpr Int HIGH = 11000000000000LL;
constexpr int LAST = 127;
constexpr int LOW = 4 * LAST * LAST * LAST;
constexpr int WHEEL = 8 * 3 * 5 * 7 * 11 * 13 * 17;
constexpr int RECORD = 253507;
std::vector<int> primes;
std::vector<bool> small_prime;
std::array<std::array<bool, LAST>, LAST + 1> square{};

void prepare_primes() {
    // LOW exceeds sqrt(HIGH) and every auxiliary prime needed for direct tests.
    static_assert(Int(LOW) * LOW > HIGH);
    small_prime.assign(LOW + 1, true);
    small_prime[0] = small_prime[1] = false;
    for (int n = 2; n <= LOW; ++n) {
        if (!small_prime[n]) continue;
        primes.push_back(n);
        if (Int(n) * n <= LOW)
            for (int j = n * n; j <= LOW; j += n) small_prime[j] = false;
        if (n <= LAST)
            for (int j = 1; j < n; ++j) square[n][j*j % n] = true;
    }
}

bool is_prime(Int n) {
    if (n <= LOW) return small_prime[n];
    for (Int q : primes) {
        if (q*q > n) return true;
        if (n % q == 0) return false;
    }
    throw std::logic_error("insufficient primes");
}

// For an odd prime p = 3 (mod 4), quadratic reciprocity gives (q/p)=(-p/q).
bool splits(Int p, int q) {
    if (q == 2) return p % 8 == 7;
    const int neg = (q - p % q) % q;
    if (q <= LAST) return square[q][neg];
    int exponent = (q-1)/2;
    Int base = neg, value = 1;
    while (exponent) {
        if (exponent & 1) value = value * base % q;
        base = base * base % q;
        exponent /= 2;
    }
    return value == 1;
}

bool has_strict_witness(Int p) {
    for (int q : primes) {
        Int cube = Int(q)*q*q;
        if (4*cube >= p) return false;
        if (splits(p, q) && (Int(q)*q + q + 1) % p &&
            (Wide(cube)*cube + cube + 1) % p) return true;
    }
    throw std::logic_error("insufficient auxiliary primes");
}

// Collect prime factors of q^2+q+1 and q^6+q^3+1 for the small sieve primes.
// Any exceptional p discarded by the periodic masks is checked here.
void factor_exceptions(Int n, std::set<Int>& exceptions) {
    for (Int r : primes) {
        if (r*r > n) break;
        if (n % r) continue;
        if (r > LOW && r <= HIGH && r%4 == 3) exceptions.insert(r);
        do { n /= r; } while (n%r == 0);
    }
    if (n > LOW && n <= HIGH && n%4 == 3) exceptions.insert(n);
}

int main() {
    prepare_primes();
    Int direct_count = 0;
    for (int p : primes) {
        if (p <= RECORD || p%4 != 3) continue;
        ++direct_count;
        if (!has_strict_witness(p)) { std::cerr << "survivor " << p << '\n'; return 1; }
    }
    std::set<Int> exceptions;
    for (int q : primes) {
        if (q > LAST) break;
        Int cube = Int(q)*q*q;
        factor_exceptions(Int(q)*q+q+1, exceptions);
        factor_exceptions(cube*cube+cube+1, exceptions);
    }
    for (Int p : exceptions)
        if (!has_strict_witness(p)) { std::cerr << "exceptional survivor " << p << '\n'; return 1; }

    std::vector<int> residues;
    for (int a = 3; a < WHEEL; a += 8) {
        bool allowed = true;
        for (int q : {3,5,7,11,13,17})
            if (a%q == 0 || splits(a,q)) allowed = false;
        if (allowed) residues.push_back(a);
    }

    Int mask_count = 0, mask_primes = 0, survivors = 0;
    #pragma omp parallel for schedule(static) reduction(+:mask_count,mask_primes,survivors)
    for (int i = 0; i < static_cast<int>(residues.size()); ++i) {
        int a = residues[i];
        const Int last_k = (HIGH-a)/WHEEL;
        const int words = int(last_k/64)+1;
        std::vector<Word> live(words, ~Word(0));
        // In word j, bit b represents p=a+WHEEL*(64*j+b).
        // The 64-bit mask for fixed q repeats every q words.
        for (int q : primes) {
            if (q > LAST) break;
            if (q < 19) continue;
            Word period[LAST];
            int x = a%q;
            int delta = WHEEL%q;
            for (int j = 0; j < q; ++j) {
                Word mask = 0;
                for (int b = 0; b < 64; ++b) {
                    if (x != 0 && !square[q][q-x]) mask |= Word(1)<<b;
                    x += delta;
                    if (x >= q) x -= q;
                }
                period[j] = mask;
            }
            for (int off = 0; off < words; off += q)
                for (int j = 0, count = std::min(q, words-off); j < count; ++j)
                    live[off+j] &= period[j];
        }
        for (int j = 0; j < words; ++j) {
            Word bits = live[j];
            while (bits) {
                int b = __builtin_ctzll(bits);
                bits &= bits-1;
                Int n = a + Int(WHEEL)*(Int(64)*j+b);
                if (n <= LOW || n > HIGH) continue;
                ++mask_count;
                if (is_prime(n)) {
                    ++mask_primes;
                    if (!has_strict_witness(n)) {
                        #pragma omp critical
                        std::cerr << "sieve survivor " << n << '\n';
                        ++survivors;
                    }
                }
            }
        }
    }
    std::cout << "interval (" << RECORD << ", " << HIGH << "]\n"
        << "direct primes through " << LOW << ": " << direct_count << '\n'
        << "higher exceptional primes explicitly checked: " << exceptions.size() << '\n'
        << "wheel " << WHEEL << " classes " << residues.size() << '\n'
        << "higher integers surviving masks: " << mask_count << '\n'
        << "primes among them checked directly: " << mask_primes << '\n'
        << "primes with no strict witness: " << survivors << '\n';
    return survivors != 0;
}
