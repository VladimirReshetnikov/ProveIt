// Certificate generator for the six-state shuffle theorem.
// Build: g++ -O3 -std=c++17 generate.cpp -o generate
// Run:   ./generate > certificates.tsv 2> generation.log
// Discovery code is not trusted by the independent Python verifier.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <unordered_set>
#include <vector>
using Bits = std::uint64_t;
struct RowPermutation {
    std::vector<int> image;
    std::array<int,64> map{}, inverse_map{};
};
struct Certificate {
    std::vector<int> f, g, predecessor;
};
class Generator {
    int m, full;
    std::array<Bits,64> incomparable{};
    std::vector<RowPermutation> permutations;
    std::unordered_set<Bits> covered;
    std::vector<int> columns;
    std::map<int,std::uint64_t> labelled, representatives;
    std::uint64_t visited = 0, candidates_tested = 0;

    bool dense() const {
        std::array<Bits,6> rows{};
        for (std::size_t j=0; j<columns.size(); ++j)
            for (int i=0; i<m; ++i)
                if ((columns[j]>>i)&1) rows[i] |= Bits(1)<<j;
        for (int i=0; i<m; ++i) {
            if (__builtin_popcountll(rows[i])<2) return false;
            for (int k=0; k<m; ++k)
                if (i!=k && (rows[i]&rows[k])==rows[i]) return false;
        }
        return true;
    }
    bool creates_balanced_triple(int s) const {
        for (std::size_t i=0; i<columns.size(); ++i)
            for (std::size_t j=i+1; j<columns.size(); ++j) {
                int u=columns[i], v=columns[j];
                if ((u|v)==(u|s) && (u|v)==(v|s)) return true;
            }
        return false;
    }
    Certificate search() {
        int n=int(columns.size()), size=0;
        for (int s:columns) size+=__builtin_popcount(unsigned(s));
        std::vector<int> pre(n), vertical(n), g(n), inverse_g(n);
        for (const auto& f:permutations) {
            for (int j=0; j<n; ++j) vertical[j]=f.inverse_map[columns[j]];
            std::iota(g.begin(),g.end(),0);
            do {
                ++candidates_tested;
                for (int j=0; j<n; ++j) inverse_g[g[j]]=j;
                int support=0, pre_size=0;
                bool good=true;
                for (int j=0; j<n; ++j) {
                    pre[j]=vertical[j]&columns[g[j]];
                    if (pre[j]==0) {good=false; break;}
                    support|=pre[j];
                    pre_size+=__builtin_popcount(unsigned(pre[j]));
                }
                if (!good || support!=full) continue;
                for (int j=0; j<n; ++j)
                    if ((f.map[pre[j]]|pre[inverse_g[j]])!=columns[j]) {
                        good=false; break;
                    }
                if (!good) continue;
                if (pre_size==size) {
                    bool removed=false;
                    for (int j=0; j<n && !removed; ++j)
                        for (int i=0; i<m && !removed; ++i)
                            if (((pre[j]>>i)&1) && (f.image[i]!=i || g[j]!=j)) {
                                pre[j]&=~(1<<i); removed=true;
                            }
                    if (!removed) continue;
                }
                return {f.image,g,pre};
            } while (std::next_permutation(g.begin(),g.end()));
        }
        throw std::runtime_error("no permutation certificate found");
    }
    void process(Bits family) {
        int n=int(columns.size());
        if (n<m || !dense()) return;
        ++labelled[n];
        if (covered.count(family)) return;
        ++representatives[n];
        Certificate c=search();
        std::cout<<m<<' '<<n<<' '<<family<<" |";
        for (int s:columns) std::cout<<' '<<s;
        std::cout<<" |"; for (int x:c.f) std::cout<<' '<<x;
        std::cout<<" |"; for (int x:c.g) std::cout<<' '<<x;
        std::cout<<" |"; for (int x:c.predecessor) std::cout<<' '<<x;
        std::cout<<'\n';
        for (const auto& p:permutations) {
            Bits renamed=0;
            for (int s:columns) renamed|=Bits(1)<<p.map[s];
            covered.insert(renamed);
        }
    }
    void visit(Bits candidates, Bits family) {
        ++visited;
        process(family);
        while (candidates) {
            int s=__builtin_ctzll(candidates);
            candidates &= candidates-1;
            if (creates_balanced_triple(s)) continue;
            columns.push_back(s);
            visit(candidates&incomparable[s], family|(Bits(1)<<s));
            columns.pop_back();
        }
    }
public:
    explicit Generator(int rows):m(rows),full((1<<rows)-1) {
        for (int s=0; s<=full; ++s)
            for (int t=0; t<=full; ++t)
                if ((s&t)!=s && (s&t)!=t) incomparable[s]|=Bits(1)<<t;
        std::vector<int> p(m); std::iota(p.begin(),p.end(),0);
        do {
            RowPermutation perm; perm.image=p;
            for (int s=0; s<=full; ++s) {
                for (int i=0; i<m; ++i) if ((s>>i)&1) perm.map[s]|=1<<p[i];
                perm.inverse_map[perm.map[s]]=s;
            }
            permutations.push_back(perm);
        } while (std::next_permutation(p.begin(),p.end()));
    }
    void run() {
        Bits candidates=0;
        for (int s=1; s<full; ++s)
            if (__builtin_popcount(unsigned(s))>=2) candidates|=Bits(1)<<s;
        visit(candidates,0);
        for (const auto& [n,count]:labelled)
            std::cerr<<"m="<<m<<" n="<<n<<" labelled="<<count
                     <<" representatives="<<representatives[n]<<'\n';
        std::cerr<<"m="<<m<<" visited="<<visited<<" orbit_coverage="<<covered.size()
                 <<" search_candidates="<<candidates_tested<<'\n';
    }
};
int main() {
    try {
        std::cout<<"# m n family_key | target_columns | row_permutation | column_permutation | predecessor_columns\n";
        for (int m=2; m<=6; ++m) Generator(m).run();
    } catch (const std::exception& e) {
        std::cerr<<"ERROR: "<<e.what()<<'\n'; return 1;
    }
}
