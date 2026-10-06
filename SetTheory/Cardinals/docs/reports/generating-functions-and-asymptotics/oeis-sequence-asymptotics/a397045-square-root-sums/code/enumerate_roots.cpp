// Report172: exact-enclosure enumeration. No floating membership decisions.
// Usage: enumerate_roots MAX_N [BITS], where 0<=MAX_N<=35, 1<=BITS<=48.
// IMPORTANT: MAX_N=35 visits 428,363,342 vectors and is never a default build.
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
using U = std::uint64_t;
using W = __uint128_t;
static U Q, cutoff, nodes=0;
static std::vector<U> weights, counts;
static U parse(const char* raw, U maximum) {
    std::string s(raw);
    if(s.empty()) throw std::runtime_error("empty argument");
    U n=0;
    for(char c:s) {
        if(c<'0'||c>'9'||n>maximum/10) throw std::runtime_error("invalid integer argument");
        n=n*10+U(c-'0');
        if(n>maximum) throw std::runtime_error("integer argument outside admitted range");
    }
    return n;
}
static U root_lower(U d) {
    // Binary-search isqrt(d*Q^2) with a 128-bit exact product.
    const W target=W(d)*Q*Q;
    U low=0, high=36*Q;
    while(low+1<high) {
        U mid=low+(high-low)/2;
        if(W(mid)*mid<=target) low=mid; else high=mid;
    }
    return low;
}
static void walk(std::size_t start,U lo,U hi) {
    if(lo>=cutoff) return;
    if(lo/Q!=hi/Q) throw std::runtime_error("ambiguous integer boundary: aborting without a result");
    if(nodes==std::numeric_limits<U>::max() || counts.at(lo/Q)==std::numeric_limits<U>::max())
        throw std::runtime_error("counter overflow: aborting without a result");
    counts.at(lo/Q)++;
    nodes++;
    for(std::size_t k=start;k<weights.size();++k) {
        if(lo+weights[k]>=cutoff) break;
        // At 1<=BITS<=48 the lower weight is >=Q, so depth <=35.
        // Each sum is < 37*2^48 plus 36 endpoint units: no uint64_t overflow.
        walk(k,lo+weights[k],hi+weights[k]+1);
    }
}
int main(int argc,char** argv) {
    try {
        if(argc<2||argc>3) throw std::runtime_error("usage: enumerate_roots MAX_N [BITS]");
        U n=parse(argv[1],35), bits=argc==3?parse(argv[2],48):48;
        if(bits==0) throw std::runtime_error("BITS must be positive");
        Q=U(1)<<bits; cutoff=(n+1)*Q;
        std::size_t bound=std::size_t((n+1)*(n+1));
        std::vector<bool> sf(bound,true);
        for(std::size_t d=2;d*d<bound;++d)
            for(std::size_t j=d*d;j<bound;j+=d*d) sf[j]=false;
        for(std::size_t d=2;d<bound;++d) if(sf[d]) weights.push_back(root_lower(d));
        counts.resize(n+1);
        walk(0,0,0);
        std::cout<<"{\"status\":\"PASS\",\"max_n\":"<<n<<",\"scale_bits\":"<<bits
                 <<",\"vectors\":"<<nodes<<",\"generators\":"<<weights.size()
                 <<",\"ambiguous_comparisons\":0,\"prefix\":[";
        U total=0;
        for(U j=0;j<=n;++j) { total+=counts[j]; if(j) std::cout<<','; std::cout<<total; }
        std::cout<<"]}\n";
        return 0;
    } catch(const std::exception& e) {
        std::cerr<<"error: "<<e.what()<<'\n';
        return 2;
    }
}
