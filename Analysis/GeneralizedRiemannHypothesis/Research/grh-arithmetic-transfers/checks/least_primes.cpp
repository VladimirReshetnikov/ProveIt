// Count earlier primes in class 1 mod q for every relevant exponent e.
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using U = std::uint64_t;

int main() {
    constexpr unsigned limit=10000000;
    std::vector<char> sieve(limit+1,true);
    std::vector<unsigned> primes;
    for (unsigned d=2; d<=limit; ++d) {
        if (!sieve[d]) continue;
        primes.push_back(d);
        for (U k=U(d)*d; k<=limit; k+=d) sieve[k]=false;
    }
    auto is_prime = [&](U n) {
        for (unsigned d : primes) {
            if (U(d)*d>n) return true;
            if (n%d==0) return false;
        }
        throw std::logic_error("trial division exhausted");
    };
    unsigned max_multiplier=0,record_q=0;
    U max_witness=0, powers_checked=0;
    constexpr U limit_p_minus_one=200000000000000ULL;
    for (unsigned q : primes) {
        unsigned multiplier=(q==2 ? 1 : 2);
        while (multiplier<q && !is_prime(U(multiplier)*q+1))
            multiplier+=2;
        if (multiplier>=q) throw std::runtime_error("threshold not met");
        const U witness=U(multiplier)*q+1;
        if (!(witness<U(q)*q)) throw std::logic_error("square bound");
        if (multiplier>max_multiplier) {
            max_multiplier=multiplier; record_q=q;
        }
        if (witness>max_witness) max_witness=witness;
        U power=U(q)*q;
        ++powers_checked;
        while (power<=limit_p_minus_one/q) {
            power*=q;
            do {
                multiplier+=(q==2 ? 1 : 2);
            } while (!is_prime(U(multiplier)*q+1));
            if (U(multiplier)*q+1 >= power)
                throw std::runtime_error("insufficient earlier primes");
            ++powers_checked;
        }
    }
    std::cout << "prime_moduli=" << primes.size()
              << " max_multiplier=" << max_multiplier << " attained_first_at_q="
              << record_q << " largest_least_prime=" << max_witness
              << " prime_powers_checked=" << powers_checked << '\n';
}
