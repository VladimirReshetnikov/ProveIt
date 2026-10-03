// Apéry Hankel norm experiments. GMP floating point, not interval arithmetic.
// Build: g++ -O3 -std=c++17 moment_norms.cpp -lgmpxx -lgmp -o moment_norms
// Usage: ./moment_norms [max_n=200] [bits=4096] > norms.csv
#include <gmpxx.h>
#include <iostream>
#include <iomanip>
#include <vector>
#include <stdexcept>
#include <string>
using F = mpf_class;
using Z = mpz_class;

std::vector<F> pivots(const std::vector<F>& moments, int n) {
    std::vector<std::vector<F>> a(n+1, std::vector<F>(n+1));
    for(int i=0;i<=n;++i) for(int j=0;j<=i;++j) a[i][j]=moments[i+j];
    std::vector<F> h(n+1);
    for(int k=0;k<=n;++k) {
        h[k]=a[k][k];
        if(h[k]<=0) throw std::runtime_error("Nonpositive pivot: increase precision.");
        for(int i=k+1;i<=n;++i) {
            F multiplier=a[i][k]/h[k];
            for(int j=i;j<=n;++j) a[j][i]-=multiplier*a[j][k];
        }
    }
    return h;
}
int main(int argc,char**argv) {
  try {
    int n=argc>1?std::stoi(argv[1]):200;
    unsigned long bits=argc>2?std::stoul(argv[2]):4096;
    if(n<1 || n>2000 || bits<128) throw std::invalid_argument("Require 1<=n<=2000 and bits>=128.");
    mpf_set_default_prec(bits);
    F root2; mpf_sqrt_ui(root2.get_mpf_t(),2);
    F C=17+12*root2, lambda=C/4;
    std::vector<Z> A(2*n+3); A[0]=1; A[1]=5;
    for(int k=1;k<2*n+2;++k) {
        // Form recurrence coefficients in Z, avoiding machine-integer overflow.
        Z z=static_cast<unsigned long>(k), next=z+1;
        Z num=(34*z*z*z+51*z*z+27*z+5)*A[k]-z*z*z*A[k-1];
        Z den=next*next*next;
        if(!mpz_divisible_p(num.get_mpz_t(),den.get_mpz_t())) throw std::runtime_error("Nonintegral Apéry recurrence.");
        mpz_divexact(A[k+1].get_mpz_t(),num.get_mpz_t(),den.get_mpz_t());
    }
    std::vector<F> m(2*n+3), mt(2*n+1), mu(2*n+1), mr(2*n+1);
    F power=1;
    for(int k=0;k<=2*n+2;++k) {m[k]=F(A[k])/power; power*=C;}
    for(int k=0;k<=2*n;++k) {mt[k]=m[k+1]; mu[k]=m[k]-m[k+1]; mr[k]=m[k+1]-m[k+2];}
    auto h=pivots(m,n), ht=pivots(mt,n), hu=pivots(mu,n), hr=pivots(mr,n);
    std::cout<<"n,U_n,E_even,E_odd,alpha_even_index,alpha_odd_index,R_previous\n"<<std::setprecision(70);
    F s=1, prevE=2;
    for(int k=0;k<=n;++k) {
        F U=s*h[k], X=4*s*ht[k], Y=4*s*hu[k];
        F Eodd=2*X*Y/(X+Y), aeven=(X-Y)/(X+Y);
        F Eeven=2, aodd=0;
        if(k>0) {
            F V=s*hr[k-1]; Eeven=2*U*V/(U+V); aodd=(U-V)/(U+V);
            if(Eeven>prevE) throw std::runtime_error("Envelope lost monotonicity; increase precision.");
        }
        if(Eodd>Eeven) throw std::runtime_error("Envelope lost interleaved monotonicity.");
        prevE=Eodd;
        std::cout<<k<<','<<U<<','<<Eeven<<','<<Eodd<<','<<aeven<<','<<aodd<<','<<lambda*U<<'\n';
        s*=16;
    }
    return 0;
  } catch(const std::exception& e) {std::cerr<<e.what()<<'\n'; return 1;}
}
