// Independent verifier for the six-row shuffle-reachability certificate.
// C++17, standard library only. No solver and no canonicalization are used.
// Usage: verify_all path/to/certificates.txt
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using U = std::uint64_t;

static int bits(U x) {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_popcountll(x);
#else
    int n=0; while(x) { x &= x-1; ++n; } return n;
#endif
}
static int first(U x) {
    if (!x) throw std::runtime_error("first(0)");
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_ctzll(x);
#else
    int i=0; while(!(x&1)) { x>>=1; ++i; } return i;
#endif
}
static void require(bool b, const std::string& message) {
    if (!b) throw std::runtime_error(message);
}
static std::vector<int> columns(U key, int m) {
    std::vector<int> c;
    while(key) { int a=first(key); key &= key-1;
        require(a<(1<<m),"column mask outside row universe"); c.push_back(a); }
    return c;
}
static bool antichain(const std::vector<int>& c) {
    for (std::size_t i=0;i<c.size();++i)
        for (std::size_t j=0;j<c.size();++j)
            if (i!=j && (c[i]&c[j])==c[i]) return false;
    return true;
}
static bool hard(const std::vector<int>& c, int m) {
    std::array<U,6> r{};
    for (std::size_t j=0;j<c.size();++j) {
        if (bits(c[j])<2) return false;
        for (int i=0;i<m;++i) if(c[j]&(1<<i)) r[i] |= U(1)<<j;
    }
    for (int i=0;i<m;++i) {
        if (bits(r[i])<2) return false;
        for (int k=0;k<m;++k)
            if (i!=k && (r[i]&r[k])==r[i]) return false;
    }
    return true;
}
struct Certificate { int m,n; U key; std::vector<int> f,g,p; };
static Certificate read_certificate(const std::string& line) {
    std::istringstream in(line); Certificate d;
    require(bool(in>>d.m>>d.n>>d.key),"bad certificate header");
    require(1<=d.m && d.m<=6,"row count out of range");
    require(1<=d.n && d.n<=64,"column count out of range");
    d.f.resize(d.m); d.g.resize(d.n); d.p.resize(d.n);
    for(int& x:d.f) require(bool(in>>x),"missing row map");
    for(int& x:d.g) require(bool(in>>x),"missing column map");
    for(int& x:d.p) require(bool(in>>x),"missing predecessor column");
    std::string extra; require(!(in>>extra),"extra certificate field");
    return d;
}
static void verify_certificate(const Certificate& d) {
    auto c=columns(d.key,d.m);
    require(int(c.size())==d.n,"key/column-count mismatch");
    require(antichain(c) && hard(c,d.m),"certificate target is not a hard antichain");
    for(int x:d.f) require(0<=x && x<d.m,"row-map value out of range");
    for(int x:d.g) require(0<=x && x<d.n,"column-map value out of range");
    int all=0,old_size=0,new_size=0;
    std::vector<int> image(d.n,0);
    for(int j=0;j<d.n;++j) {
        require(0<d.p[j] && d.p[j]<(1<<d.m),"predecessor column empty or invalid");
        all |= d.p[j]; old_size += bits(d.p[j]); new_size += bits(c[j]);
        for(int i=0;i<d.m;++i) if(d.p[j]&(1<<i)) {
            image[j] |= 1<<d.f[i];
            image[d.g[j]] |= 1<<i;
        }
    }
    require(all==(1<<d.m)-1,"predecessor has an empty row");
    require(old_size<new_size,"predecessor does not strictly decrease size");
    require(image==c,"forward image does not equal target");
}
static std::vector<U> orbit_union(const std::vector<Certificate>& ds,int m) {
    std::vector<U> covered;
    std::size_t factorial=1; for(int i=2;i<=m;++i)factorial*=i;
    covered.reserve(ds.size()*factorial);
    std::vector<int> p(m); for(int i=0;i<m;++i)p[i]=i;
    do {
        std::array<int,64> transform{};
        for(int a=0;a<(1<<m);++a)
            for(int i=0;i<m;++i)if(a&(1<<i))transform[a]|=1<<p[i];
        for(const auto& d:ds) {
            U result=0;
            for(U u=d.key;u;u&=u-1)result |= U(1)<<transform[first(u)];
            covered.push_back(result);
        }
    } while(std::next_permutation(p.begin(),p.end()));
    std::sort(covered.begin(),covered.end());
    covered.erase(std::unique(covered.begin(),covered.end()),covered.end());
    return covered;
}
struct Enumeration {
    int m; const std::vector<U>& covered;
    std::array<U,64> comparable{};
    std::vector<int> current;
    U total=0,hard_total=0;
    std::array<U,65> by_size{},hard_by_size{};
    Enumeration(int rows,const std::vector<U>& c):m(rows),covered(c) {
        current.reserve(64);
        for(int a=0;a<(1<<m);++a)
            for(int b=0;b<(1<<m);++b)
                if((a&b)==a || (a&b)==b)comparable[a] |= U(1)<<b;
    }
    void visit(U family,U available) {
        ++total; ++by_size[current.size()];
        if(hard(current,m)) {
            ++hard_total; ++hard_by_size[current.size()];
            require(std::binary_search(covered.begin(),covered.end(),family),
                    "uncovered hard family: m="+std::to_string(m)+
                    " key="+std::to_string(family));
        }
        // available contains only masks larger than all previously chosen masks.
        while(available) {
            int a=first(available); U bit=U(1)<<a; available &= ~bit;
            current.push_back(a);
            visit(family|bit,available & ~comparable[a]);
            current.pop_back();
        }
    }
    void run() {
        U universe=m==6 ? ~U(0) : (U(1)<<(1<<m))-1;
        visit(0,universe);
    }
};
int main(int argc,char** argv) {
    try {
        require(argc==2,"usage: verify_all path/to/certificates.txt");
        auto start=std::chrono::steady_clock::now();
        std::ifstream in(argv[1]); require(bool(in),"cannot open certificate file");
        std::array<std::vector<Certificate>,7> certs;
        std::string line; std::size_t count=0,line_number=0;
        while(std::getline(in,line)) {
            ++line_number;
            if(line.empty() || line[0]=='#')continue;
            try {
                auto d=read_certificate(line); verify_certificate(d);
                certs[d.m].push_back(std::move(d)); ++count;
            } catch(const std::exception& e) {
                throw std::runtime_error("line "+std::to_string(line_number)+": "+e.what());
            }
        }
        std::cout<<"Verified forward-image certificates: "<<count<<"\n";
        U total_families=0,total_hard=0;
        for(int m=1;m<=6;++m) {
            auto covered=orbit_union(certs[m],m);
            Enumeration e(m,covered); e.run();
            // Every covered key is a hard antichain; equality is an extra audit.
            require(e.hard_total==covered.size(),"coverage count mismatch");
            total_families+=e.total; total_hard+=e.hard_total;
            std::cout<<"m="<<m<<" certificates="<<certs[m].size()
                     <<" all_labeled_antichains="<<e.total
                     <<" hard_labeled_antichains="<<e.hard_total
                     <<" covered="<<covered.size()<<"\n";
            if(m==6)for(int k=0;k<=64;++k)if(e.by_size[k])
                std::cout<<"  n="<<k<<" all="<<e.by_size[k]
                         <<" hard="<<e.hard_by_size[k]<<"\n";
        }
        double seconds=std::chrono::duration<double>(
            std::chrono::steady_clock::now()-start).count();
        std::cout<<"PASS: "<<total_families<<" labeled antichains enumerated; "
                 <<total_hard<<" hard antichains covered.\n";
        std::cout<<"Elapsed seconds: "<<seconds<<"\n";
        return 0;
    } catch(const std::exception& e) {
        std::cerr<<"FAIL: "<<e.what()<<"\n"; return 1;
    }
}
