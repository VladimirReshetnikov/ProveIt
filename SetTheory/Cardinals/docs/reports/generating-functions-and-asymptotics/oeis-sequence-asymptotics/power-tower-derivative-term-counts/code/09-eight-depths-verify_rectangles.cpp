// Exact modular certificate for A290268, depths 3 through 8 (depths 5--8 are the new strata).
// No primality assumption is used. Nonzero mod m implies nonzero in Z.
// Build: c++ -O3 -std=c++17 verify_rectangles.cpp -o verify_rectangles
// Run: ./verify_rectangles > rectangle_results.json
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>
using U = std::uint64_t;
using Jet = std::vector<U>;
constexpr U M1=1000000007ULL, M2=1000000009ULL;
// Operands are reduced, so a*b < (M2-1)^2 < 2^64.
U mul(U a,U b,U m) {return (a*b)%m;}
U residue(long long x,U m) {long long y=x%static_cast<long long>(m);return static_cast<U>(y<0?y+static_cast<long long>(m):y);}
Jet linear(const Jet& a,long long c,U b,U m) {
    Jet v(a.size()); U cr=residue(c,m);
    for(std::size_t j=0;j<a.size();++j) v[j]=(mul(cr,a[j],m)+(j?mul(b,a[j-1],m):0))%m;
    return v;
}
U single_cell(int d,int k,int q,U m) {
    const int p=2*d,r=p+q+1; Jet a(d+1),prev(d+1);a[0]=1;
    for(int i=0;i<r;++i) a=linear(a,p-i,1,m);
    for(int h=0;h<k;++h) {
        Jet nxt=linear(a,p-q,2,m);U fac=mul(h%m,(h+r)%m,m);
        for(int j=0;j<=d;++j)nxt[j]=(nxt[j]+mul(fac,prev[j],m))%m;
        prev.swap(a);a.swap(nxt);
    }
    return a[d];
}
struct Result {
    int d=0,R=0,Q=0; U cells=0,holes=0,nonzero=0,first_suffices=0,second_needed=0,unresolved=0,bad_holes=0;
    std::vector<std::pair<int,int>> candidates;
};
Result verify(int d,int R,int Q) {
    Result out; out.d=d; out.R=R; out.Q=Q; const int p=2*d;
    Jet initial(d+1);initial[0]=1;
    for(int i=0;i<=p;++i) initial=linear(initial,p-i,1,M1);
    for(int q=0;q<Q;++q) {
        Jet cur=initial,prev(d+1),nxt(d+1);
        const U r=p+q+1,cr=residue(p-q,M1);
        for(int k=0;k<=R-2;++k) {
            ++out.cells;
            const bool hole=(q==p)&&((k+d)%2==0);
            if(hole) {++out.holes;if(cur[d])++out.bad_holes;}
            else if(cur[d]) {++out.nonzero;++out.first_suffices;}
            else out.candidates.emplace_back(k,q);
            const U fac=mul(k%M1,(k+r)%M1,M1);
            for(int j=0;j<=d;++j) {
                U v=mul(cr,cur[j],M1)+mul(fac,prev[j],M1)+(j?2*cur[j-1]:0);
                nxt[j]=v%M1;
            }
            prev.swap(cur);cur.swap(nxt);
        }
        initial=linear(initial,-q-1,1,M1);
    }
    for(auto [k,q]:out.candidates) {
        if(single_cell(d,k,q,M2)) {++out.nonzero;++out.second_needed;}
        else {++out.unresolved;std::cerr<<"UNRESOLVED d="<<d<<" k="<<k<<" q="<<q<<"\n";}
    }
    std::cerr<<"Completed depth "<<d<<": "<<out.cells<<" cells, "<<out.unresolved<<" unresolved.\n";
    return out;
}
void print(const Result& r) {
    std::cout<<" {\"depth\":"<<r.d<<",\"R\":"<<r.R<<",\"Q\":"<<r.Q
    <<",\"cells\":"<<r.cells<<",\"symmetry_holes\":"<<r.holes
    <<",\"certified_nonzero\":"<<r.nonzero<<",\"first_modulus_suffices\":"<<r.first_suffices
    <<",\"second_modulus_needed\":"<<r.second_needed<<",\"unresolved\":"<<r.unresolved
    <<",\"incorrect_holes\":"<<r.bad_holes<<",\"first_modulus_zero_candidates\":[";
    bool first=true;
    for(auto [k,q]:r.candidates){if(!first)std::cout<<",";first=false;std::cout<<"["<<k<<","<<q<<"]";}
    std::cout<<"]}";
}
int main() {
    try {
        std::vector<Result> r;
        r.push_back(verify(3,14,39));r.push_back(verify(4,89,192));
        r.push_back(verify(5,398,814));r.push_back(verify(6,1461,2944));
        r.push_back(verify(7,5078,10183));r.push_back(verify(8,16613,33257));
        std::cout<<"{\n\"moduli\":[1000000007,1000000009],\n\"results\":[\n";
        bool bad=false;
        for(std::size_t i=0;i<r.size();++i){if(i)std::cout<<",\n";print(r[i]);bad|=r[i].unresolved||r[i].bad_holes;}
        std::cout<<"\n],\n\"scope\":\"Finite rectangles only; analytic reduction is proved in article.tex.\"\n}\n";
        return bad?1:0;
    } catch(const std::exception& e){std::cerr<<e.what()<<"\n";return 2;}
}
