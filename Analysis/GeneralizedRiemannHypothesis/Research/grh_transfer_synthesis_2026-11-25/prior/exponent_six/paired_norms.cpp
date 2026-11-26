// g++ -O3 -std=c++17 paired_norms.cpp -o paired_norms
// ./paired_norms [largest-p-or-q=5500] [largest-character-test-prime=2000]
// Enumerates all positive integer solutions before applying the indicated
// character obstructions. An empty final survivor list excludes fundamental
// discriminants as a special case, without a primality or squarefreeness oracle.
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <map>
#include <string>
#include <utility>
#include <vector>

using u64 = std::uint64_t;
using u128 = __uint128_t;
using Exponents = std::vector<std::pair<u64,int>>;

const u128 lower = u128(310) * 1000000000000000000ULL;
const int smallest_prime = 2000;

std::string decimal(u128 x) {
    std::string s;
    do { s.push_back(char('0'+x%10)); x /= 10; } while (x);
    std::reverse(s.begin(),s.end());
    return s;
}

std::vector<int> primes(int limit) {
    std::vector<bool> is_prime(limit+1,true);
    is_prime[0] = is_prime[1] = false;
    for (int i=2; i*i<=limit;i++)
        if (is_prime[i])
            for (int j=i*i;j<=limit;j+=i) is_prime[j]=false;
    std::vector<int> out;
    for (int i=2;i<=limit;i++) if (is_prime[i]) out.push_back(i);
    return out;
}

u64 cube(u64 a) { return a*a*a; }

u64 isqrt(u128 x) {
    u64 r = static_cast<u64>(std::sqrt(static_cast<long double>(x)));
    while (u128(r)*r>x) --r;
    while (u128(r+1)*(r+1)<=x) ++r;
    return r;
}

void factor_into(u64 a, const std::vector<int>& primes, std::map<u64,int>& factors) {
    for (u64 r : primes) {
        if (r*r>a) break;
        while (a%r==0) { ++factors[r]; a/=r; }
    }
    if (a>1) ++factors[a];
}

struct Test {
    int prime;
    std::vector<bool> allowed;
};

std::vector<Test> character_tests(u64 p, const std::vector<int>& all, int sieve_max) {
    std::vector<Test> tests;
    for (int r : all) {
        if (r<=18) continue;
        if (r>sieve_max) break;
        std::vector<bool> square(r,false), allowed(r);
        for (int a=1;a<r;a++) square[a*a%r]=true;
        int doubled_cube=2*(cube(p)%r)%r;
        int constant=doubled_cube*doubled_cube%r;
        for (int a=0;a<r;a++)
            allowed[a]=!square[(a*a+r-constant)%r];
        tests.push_back({r,std::move(allowed)});
    }
    return tests;
}

struct Counters {
    u64 prime_count=0, pair_count=0, divisors_in_interval=0;
    u64 above_lower=0, after_character_sieve=0;
    int largest_first_witness=0;
};

struct PairSearch {
    u64 p,q,lo,hi;
    u128 product, four_p6;
    const Exponents& exponents;
    const std::vector<Test>& tests;
    Counters& count;

    void candidate(u64 u) {
        ++count.divisors_in_interval;
        u64 v=static_cast<u64>(product/u);
        assert(u<=v && u128(u)*v==product && v-u<=2*cube(p));
        u64 a=v-u;
        u128 y=four_p6-u128(a)*a;
        if (y<=lower) return;
        ++count.above_lower;
        for (const auto& t : tests)
            if (!t.allowed[a%t.prime]) {
                count.largest_first_witness=std::max(count.largest_first_witness,t.prime);
                return;
            }
        ++count.after_character_sieve;
        std::cout<<"survivor p="<<p<<" q="<<q<<" U="<<u<<" a="<<a
                 <<" Y="<<decimal(y)<<"\n";
    }

    void divisors(std::size_t index, u64 d) {
        if (index==exponents.size()) {
            if (d>=lo) candidate(d);
            return;
        }
        auto [r,e]=exponents[index];
        for (int k=0;k<=e;k++) {
            divisors(index+1,d);
            if (k==e || r>hi/d) break;
            d*=r;
        }
    }
};

int main(int argc,char** argv) {
    int upper=argc>1?std::stoi(argv[1]):5500;
    int sieve=argc>2?std::stoi(argv[2]):2000;
    if (upper<=smallest_prime || upper>5500 || sieve<19 || sieve>2000) return 2;
    const auto all=primes(10000); // > sqrt(3*5500^2)
    Counters count;
    for (u64 p : all) {
        if (p<smallest_prime || u128(4)*cube(p)*cube(p)<=lower) continue;
        if (p>static_cast<u64>(upper)) break;
        ++count.prime_count;
        auto tests=character_tests(p,all,sieve);
        for (u64 q : all) {
            if (q<=p) continue;
            if (q>static_cast<u64>(upper)) break;
            ++count.pair_count;
            std::map<u64,int> factors;
            for (u64 f : {q-p,q+p,q*q+p*q+p*p,q*q-p*q+p*p})
                factor_into(f,all,factors);
            u64 c=cube(p), d=cube(q);
            u128 product=u128(d)*d-u128(c)*c, check=1;
            for (auto [r,e]: factors) for (int j=0;j<e;j++) check*=r;
            assert(check==product);
            Exponents exponents(factors.rbegin(),factors.rend());
            PairSearch search{p,q,d-c,isqrt(product),product,u128(4)*c*c,
                              exponents,tests,count};
            search.divisors(0,1);
        }
    }
    std::cout<<"upper_prime="<<upper<<"\n"
             <<"sieve_max="<<sieve<<"\n"
             <<"eligible_primes="<<count.prime_count<<"\n"
             <<"prime_pairs="<<count.pair_count<<"\n"
             <<"divisors_in_closed_interval="<<count.divisors_in_interval<<"\n"
             <<"Y_above_lower_bound="<<count.above_lower<<"\n"
             <<"largest_first_split_witness="<<count.largest_first_witness<<"\n"
             <<"Y_after_character_sieve="<<count.after_character_sieve<<"\n";
    return count.after_character_sieve == 0 ? 0 : 1;
}
