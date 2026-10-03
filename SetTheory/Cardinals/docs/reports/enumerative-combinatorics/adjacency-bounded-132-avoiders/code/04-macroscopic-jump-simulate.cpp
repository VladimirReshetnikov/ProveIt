// Uniform Catalan sampling by the cycle lemma. C++17, no external libraries.
// Reproducible pseudorandom illustrations, NOT mathematical certificates.
// Build: g++ -O3 -std=c++17 code/simulate.cpp -o simulate
// Run: ./simulate > data/simulation.csv
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <random>
#include <vector>
struct Stat { int n, first, last, maximum; };
Stat merge(Stat l, Stat r) {
    int n=l.n+r.n+1;
    int f=l.n ? r.n+l.first : n;
    if (r.n) return {n,f,r.last,std::max(n-r.first,r.maximum)};
    return {n,f,n,l.n ? std::max(l.maximum,n-l.last) : 0};
}
int main() {
    std::mt19937_64 rng(20260929ULL);
    const std::array<std::pair<int,int>,5> jobs={{{64,300000},{256,200000},
                                               {1024,100000},{4096,50000},
                                               {16384,25000}}};
    const std::array<double,5> cuts={{0.10,0.20,0.30,0.40,0.55}};
    std::cout<<"n,samples,mean_over_sqrt_n,mean_standard_error,second_moment_scaled";
    for (double u:cuts) std::cout<<",scaled_tail_"<<u<<",tail_standard_error_"<<u;
    std::cout<<"\n"<<std::setprecision(12);
    for (auto [n,samples]:jobs) {
        std::vector<int> word(2*n+1);
        std::fill(word.begin(),word.begin()+n,1);
        std::fill(word.begin()+n,word.end(),-1);
        std::vector<Stat> stack; stack.reserve(n+1);
        long double sum=0,sum2=0;
        std::array<int,5> tails{};
        for (int rep=0;rep<samples;++rep) {
            std::shuffle(word.begin(),word.end(),rng);
            int total=0,low=0,start=0;
            for (int i=0;i<int(word.size());++i) {
                total+=word[i];
                if (total<low) {low=total;start=i+1;}
            }
            start%=int(word.size()); stack.clear();
            for (int j=int(word.size())-1;j>=0;--j) {
                int k=start+j; if (k>=int(word.size())) k-=int(word.size());
                if (word[k]==-1) stack.push_back({0,0,0,0});
                else {
                    Stat left=stack.back();stack.pop_back();
                    Stat right=stack.back();stack.pop_back();
                    stack.push_back(merge(left,right));
                }
            }
            if (stack.size()!=1 || stack[0].n!=n) {std::cerr<<"invalid tree\n";return 2;}
            int d=n-stack[0].maximum;
            sum+=d;sum2+=static_cast<long double>(d)*d;
            for (unsigned j=0;j<cuts.size();++j) if (d>cuts[j]*n) ++tails[j];
        }
        long double mean=sum/samples,second=sum2/samples;
        long double variance=(second-mean*mean)*samples/(samples-1);
        std::cout<<n<<','<<samples<<','<<double(mean/std::sqrt(n))<<','
                 <<double(std::sqrt(variance/(samples*n)))<<','
                 <<double(second/(n*std::sqrt(n)));
        for (int c:tails) {
            double p=double(c)/samples;
            std::cout<<','<<std::sqrt(n)*p<<','<<std::sqrt(n*p*(1-p)/samples);
        }
        std::cout<<'\n'<<std::flush;
    }
}
