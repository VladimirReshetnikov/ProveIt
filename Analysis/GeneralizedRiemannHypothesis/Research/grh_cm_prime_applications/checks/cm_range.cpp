// Certify four factor-16-separated conjugates for 10^7 <= |Delta| < 10^11.
// g++ -O3 -std=c++17 cm_range.cpp -o cm_range && ./cm_range
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

using Int = std::int64_t;
using Wide = __int128_t;
std::vector<int> primes;
std::vector<std::vector<bool>> splits;
std::vector<int> wheel;
Int lo, hi, by_two, by_wheel, by_primes, by_forms, failed;

bool separated(Int d, Int a, Int b) {
    return d >= 16*a*a && Wide(9)*d*(b-a)*(b-a) >= Wide(16)*a*a*b*b;
}

bool has_reduced_form(Int d, Int a) {
    // Both signs of b have the same integrality, primitivity and reducedness.
    for (Int b=d%2; b<=a; b+=2) {
        Int numerator=d+b*b;
        if (numerator%(4*a)) continue;
        Int c=numerator/(4*a);
        if (a<=c && std::gcd(std::gcd(a,b),c)==1) return true;
    }
    return false;
}

void certify(Int d) {
    Int a=1;
    int count=1;
    for (unsigned i=1; i<primes.size(); ++i) {
        int p=primes[i];
        if (4LL*p*p>d) break;
        if (separated(d,a,p) && splits[i][d%p]) {
            a=p;
            if (++count==4) { ++by_primes; return; }
        }
    }
    a=1;
    count=1;
    for (Int b=2; b<=2000 && 4*b*b<=d; ++b) {
        if (separated(d,a,b) && has_reduced_form(d,b)) {
            a=b;
            if (++count==4) { ++by_forms; return; }
        }
    }
    std::cout << "Uncertified " << d << '\n';
    ++failed;
}

Int first_in_bin(Int residue, Int modulus) {
    if (residue>=lo) return residue;
    return residue+((lo-residue+modulus-1)/modulus)*modulus;
}

Int count_in_bin(Int residue, Int modulus) {
    Int first=first_in_bin(residue,modulus);
    return first>=hi ? 0 : 1+(hi-1-first)/modulus;
}

void visit(Int residue, Int modulus, unsigned level) {
    if (residue>=hi) return;
    if (level==wheel.size() || modulus>=hi) {
        for (Int d=first_in_bin(residue,modulus); d<hi; d+=modulus) {
            bool covered=false;
            for (unsigned j=level; j<wheel.size(); ++j) {
                int i=wheel[j];
                if (splits[i][d%primes[i]]) { covered=true; break; }
            }
            if (covered) ++by_wheel;
            else certify(d);
        }
        return;
    }
    int i=wheel[level], p=primes[i];
    for (int t=0; t<p; ++t) {
        Int r=residue+t*modulus;
        if (r>=hi) break;
        if (splits[i][r%p]) by_wheel+=count_in_bin(r,modulus*p);
        else visit(r,modulus*p,level+1);
    }
}

int main() {
    for (int p=2;p<1000;++p) {
        bool prime=true;
        for (int r=2;r*r<=p;++r)
            if (p%r==0) { prime=false; break; }
        if (!prime) continue;
        primes.push_back(p);
        splits.emplace_back(p,false);
        // -d is a nonzero square mod p.
        for (int k=1;k<p;++k) splits.back()[(p-k*k%p)%p]=true;
    }
    constexpr Int end=100000000000LL;
    std::cout << "lower upper split2 wheel split_primes direct_forms failed\n";
    for (lo=10000000;lo<end;lo=hi) {
        hi=std::min(end,2*lo);
        wheel.clear();
        for (unsigned j=1;j<primes.size();++j) {
            Int p=primes[j];
            if (Wide(4)*p*p*p*p*p*p>lo) break;
            wheel.push_back(j);
        }
        by_two=count_in_bin(7,8);
        by_wheel=by_primes=by_forms=failed=0;
        for (int r:{0,3,4}) visit(r,8,0);
        Int total=count_in_bin(0,4)+count_in_bin(3,4);
        if (total!=by_two+by_wheel+by_primes+by_forms+failed || failed)
            throw std::runtime_error("Incomplete discrimination range");
        std::cout <<lo<<' '<<hi<<' '<<by_two<<' '<<by_wheel<<' '
                  <<by_primes<<' '<<by_forms<<' '<<failed<<std::endl;
    }
}
