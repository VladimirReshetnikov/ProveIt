// Independent exhaustive comparison: direct graph predicate vs. Boolean flags.
// Build: g++ -O3 -std=c++17 exhaustive.cpp -o exhaustive
// Run:   ./exhaustive 8 > ../data/exhaustive.json
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>

using Word = std::uint32_t;

bool flags_visible(Word mask, int n) {
    if (n == 1) return true;
    const int N = 3*n-1;
    const Word full = (Word(1)<<N)-1;
    if (mask == full) return false;
    const int z = __builtin_ctz((~mask)&full);
    Word flags = 0;
    int previous = z;
    for (int step=1; step<N; ++step) {
        const int current = (previous+3)%N;
        const int before = (current+N-1)%N;
        if (((mask>>current)&1) && (((mask>>before)&1) || ((flags>>previous)&1)))
            flags |= Word(1)<<current;
        previous = current;
    }
    const Word next_bits = (mask>>1) | ((mask&1)<<(N-1));
    return (flags & next_bits) == 0;
}

int main(int argc, char** argv) {
    const int limit = argc > 1 ? std::stoi(argv[1]) : 8;
    if (limit < 1 || limit > 9) throw std::invalid_argument("require 1<=limit<=9");
    const auto start = std::chrono::steady_clock::now();
    std::uint64_t tested = 0;
    std::cout << "{\n  \"method\": \"all subsets: direct graph vs flags\",\n  \"rows\": [\n";
    for (int n=1; n<=limit; ++n) {
        const int N=3*n-1;
        std::vector<Word> neighbors(N,0);
        for (int a=0; a<N; ++a)
            for (int d=1; d<N; d+=3) neighbors[a] |= Word(1)<<((a+d)%N);
        std::set<Word> graph_obstructions, word_obstructions;
        for (int a=0; a<N; ++a) for (int b=a+1; b<N; ++b) {
            if ((neighbors[a]>>b)&1) continue;
            const Word common=neighbors[a]&neighbors[b];
            if (!common) throw std::runtime_error("diameter-two test failed");
            graph_obstructions.insert(common | (Word(1)<<a) | (Word(1)<<b));
        }
        for (int a=0; a<N; ++a) for (int r=1; r<n; ++r) {
            Word obstruction = (Word(1)<<a) | (Word(1)<<((a+3*r-1)%N));
            for (int j=0; j<r; ++j) obstruction |= Word(1)<<((a+1+3*j)%N);
            word_obstructions.insert(obstruction);
        }
        if (graph_obstructions != word_obstructions)
            throw std::runtime_error("obstruction families differ");
        std::vector<Word> obstructions(graph_obstructions.begin(),graph_obstructions.end());
        std::sort(obstructions.begin(),obstructions.end(),[](Word a,Word b){
            return __builtin_popcount(a)<__builtin_popcount(b);
        });
        std::vector<std::uint64_t> coefficients(N+1,0);
        const Word end=Word(1)<<N;
        for (Word mask=0; mask<end; ++mask) {
            bool direct=true;
            for (Word obstruction: obstructions)
                if ((mask&obstruction)==obstruction) { direct=false; break; }
            const bool flags=flags_visible(mask,n);
            if (direct!=flags) {
                std::cerr<<"Mismatch n="<<n<<" mask="<<mask<<"\n";
                return 2;
            }
            if (direct) ++coefficients[__builtin_popcount(mask)];
        }
        tested += end;
        while (coefficients.size()>1 && coefficients.back()==0) coefficients.pop_back();
        std::uint64_t total=0;
        for (auto c:coefficients) total+=c;
        std::cout<<"    {\"n\": "<<n<<", \"vertices\": "<<N
                 <<", \"subsets_tested\": "<<end<<", \"total\": "<<total<<", \"coefficients\": [";
        for (std::size_t i=0;i<coefficients.size();++i) {
            if(i) std::cout<<", ";
            std::cout<<coefficients[i];
        }
        std::cout<<"]}"<<(n==limit?"\n":",\n");
        std::cerr<<"n="<<n<<" checked "<<end<<" subsets; total="<<total<<"\n";
    }
    const double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout<<"  ],\n  \"subsets_tested\": "<<tested<<",\n  \"mismatches\": 0,\n  \"elapsed_seconds\": "<<seconds<<"\n}\n";
}
