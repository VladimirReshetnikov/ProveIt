// Exact Eratosthenes check of two common windows, using C++17.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using U = std::uint64_t;

std::vector<char> prime_segment(U start, unsigned length) {
    const U last = start + length - 1;
    unsigned limit = 0;
    while (U(limit+1)*(limit+1) <= last) ++limit;
    std::vector<char> base(limit+1,true), prime(length,true);
    for (unsigned d=2; d<=limit; ++d) {
        if (!base[d]) continue;
        for (U k=U(d)*d; k<=limit; k+=d) base[k]=false;
        U first = std::max(U(d)*d, ((start+d-1)/d)*d);
        for (U k=first; k<=last; k+=d) prime[k-start]=false;
    }
    return prime; // both requested segments begin above 2
}

void verify(U start, int t) {
    constexpr unsigned length=25000000;
    const auto prime=prime_segment(start,length);
    U count=0, maxprime=0;
    unsigned record_q=0,record_a=0;
    for (unsigned q=45001; q<=50000; ++q) {
        U lower=(t==1 ? U(q) : U(q)*q), upper=lower*q;
        if (start<lower || start+length>upper) throw std::logic_error("range");
        const unsigned shift=start % q;
        for (unsigned a=1; a<q; ++a) {
            if (std::gcd(a,q)!=1) continue;
            unsigned i=(a+q-shift)%q;
            while (i<length && !prime[i]) i+=q;
            if (i>=length) throw std::runtime_error("uncovered class");
            ++count;
            if (start+i>maxprime) {
                maxprime=start+i; record_q=q; record_a=a;
            }
        }
    }
    std::cout << "t=" << t << " pairs=" << count << " largest_first_witness="
              << maxprime << " q=" << record_q << " a=" << record_a << '\n';
}

int main() {
    verify(50001,1);
    verify(2500000001,2);
}
