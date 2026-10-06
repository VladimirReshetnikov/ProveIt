#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
using Perm = vector<int>;

// Independent validation: count all increasing subsequences of length five,
// retaining the sole chain when the count is exactly one. Values are one-based.
int five_count(const Perm &v, Perm *chain = nullptr) {
    vector<array<long long,6>> ways(v.size());
    vector<array<int,6>> prev(v.size());
    long long total = 0;
    int endpoint = -1;
    for (int i=0; i<(int)v.size(); ++i) {
        ways[i].fill(0); prev[i].fill(-1); ways[i][1]=1;
        for (int j=0; j<i; ++j) if (v[j]<v[i])
            for (int k=2; k<=5; ++k) if (ways[j][k-1]) {
                ways[i][k]+=ways[j][k-1];
                prev[i][k]=j;
            }
        total+=ways[i][5];
        if (ways[i][5]) endpoint=i;
    }
    if (total==1 && chain) {
        chain->resize(5);
        for (int k=5; k>=1; --k) {
            (*chain)[k-1]=endpoint;
            endpoint=prev[endpoint][k];
        }
    }
    return total>1 ? 2 : (int)total;
}

bool avoids_three(const Perm &v) {
    for (int j=0; j<(int)v.size(); ++j) {
        bool smaller=false, larger=false;
        for (int i=0; i<j; ++i) smaller |= v[i]<v[j];
        for (int k=j+1; k<(int)v.size(); ++k) larger |= v[j]<v[k];
        if (smaller && larger) return false;
    }
    return true;
}

Perm standardize(const Perm &v) {
    Perm sorted=v, out;
    sort(sorted.begin(),sorted.end());
    for (int x:v) out.push_back(lower_bound(sorted.begin(),sorted.end(),x)-sorted.begin()+1);
    return out;
}

struct Boundary { Perm beta; int p,q; };
Boundary erase_marks(const Perm &v,const Perm &c) {
    Perm kept;
    for (int i=0;i<(int)v.size();++i) if(i!=c[1]&&i!=c[3]) kept.push_back(v[i]);
    Boundary b{standardize(kept), (int)v.size()-c[1]-2, v[c[3]]-2};
    return b;
}

bool boundary_valid(const Boundary &b, int *pivot=nullptr) {
    int m=b.beta.size();
    if(b.p<2||b.p>m||b.q<2||b.q>m||five_count(b.beta)) return false;
    Perm suffix(b.beta.end()-b.p,b.beta.end()), low;
    for(int x:b.beta) if(x<=b.q)low.push_back(x);
    if(!avoids_three(suffix)||!avoids_three(low))return false;
    int meet=-1, count=0;
    for(int i=m-b.p;i<m;++i)if(b.beta[i]<=b.q){meet=i;++count;}
    if(count!=1||meet==m-1||b.beta[meet]==1)return false;
    if(pivot)*pivot=meet;
    return true;
}

Perm insert_rank(const Perm &v,int offset,int rank) {
    Perm out=v;
    for(int &x:out)if(x>=rank)++x;
    out.insert(out.begin()+offset,rank);
    return out;
}

Perm inflate(const Boundary &b) {
    Perm v=insert_rank(b.beta,b.beta.size()-b.p,2);
    return insert_rank(v,v.size()-1,b.q+2);
}

struct Disjoint { Perm gamma; int P,Q,R,T; };
bool decreasing(const Perm &v) {
    for(int i=1;i<(int)v.size();++i)if(v[i-1]<v[i])return false;
    return true;
}

bool disjoint_valid(const Disjoint &g) {
    int m=g.gamma.size();
    if(g.P<1||g.Q<1||g.R<1||g.T<1||g.R>g.P||g.T>g.Q||g.P+g.Q>m)
        return false;
    if(five_count(g.gamma))return false;
    Perm suffix(g.gamma.end()-g.P,g.gamma.end());
    Perm tail(g.gamma.end()-g.R,g.gamma.end()),low,tiny;
    for(int x:suffix)if(x<=g.Q)return false;
    for(int x:g.gamma){if(x<=g.Q)low.push_back(x);if(x<=g.T)tiny.push_back(x);}
    return avoids_three(suffix)&&avoids_three(low)&&decreasing(tail)&&decreasing(tiny);
}

Boundary add_pivot(const Disjoint &g) {
    return Boundary{insert_rank(g.gamma,g.gamma.size()-g.R,g.T+1),g.P+1,g.Q+1};
}

Disjoint erase_pivot(const Boundary &b) {
    int pivot;
    if(!boundary_valid(b,&pivot))abort();
    Perm kept=b.beta;kept.erase(kept.begin()+pivot);
    return Disjoint{standardize(kept),b.p-1,b.q-1,(int)b.beta.size()-pivot-1,b.beta[pivot]-1};
}

bool northern(const Perm &v,const Perm &c,array<int,4> *stat=nullptr) {
    array<int,4> k{};
    for(int i=0;i<(int)v.size();++i) {
        if(find(c.begin(),c.end(),i)!=c.end())continue;
        int a=0,b=0;
        for(int j:c){a+=j<i;b+=v[j]<v[i];}
        if(b-a<2)return false;
        if(a==2||a==3)++k[a-2];
        if(b==2||b==3)++k[b];
    }
    if(stat)*stat=k;
    return true;
}

[[noreturn]] void fail(const string &why,const Perm &v,int p=-1,int q=-1) {
    cerr<<"FAIL "<<why<<"; permutation:";
    for(int x:v)cerr<<' '<<x;
    cerr<<" p="<<p<<" q="<<q<<'\n';exit(1);
}

int main(int argc,char **argv) {
    int N=argc>1?atoi(argv[1]):10;
    for(int n=5;n<=N;++n) {
        long long halves=0,boundaries=0,disjoints=0;
        Perm v(n);iota(v.begin(),v.end(),1);
        do {
            Perm c;
            if(five_count(v,&c)!=1||!northern(v,c))continue;
            ++halves;
            Boundary b=erase_marks(v,c);
            if(!boundary_valid(b))fail("forward image fails boundary conditions",v,b.p,b.q);
            if(inflate(b)!=v)fail("inverse(forward(v)) differs as an object",v,b.p,b.q);
        }while(next_permutation(v.begin(),v.end()));
        int m=n-2;
        Perm beta(m);iota(beta.begin(),beta.end(),1);
        do {
            if(five_count(beta))continue;
            for(int p=2;p<=m;++p)for(int q=2;q<=m;++q) {
                Boundary b{beta,p,q};int pivot;
                if(!boundary_valid(b,&pivot))continue;
                ++boundaries;
                Perm inflated=inflate(b),c;array<int,4> stat;
                if(five_count(inflated,&c)!=1)fail("inflation is not unique-12345",beta,p,q);
                if(!northern(inflated,c,&stat))fail("inflation is not northern",beta,p,q);
                // Check the intended marked spine, not just the resulting class.
                int minpos=find(beta.begin(),beta.end(),1)-beta.begin();
                Perm intended{minpos,m-p,pivot+1,m,m+1};
                if(c!=intended)fail("the recovered unique spine differs",beta,p,q);
                Boundary returned=erase_marks(inflated,c);
                if(returned.beta!=beta||returned.p!=p||returned.q!=q)
                    fail("forward(inverse(b)) differs as an object",beta,p,q);
                array<int,4> expected{pivot-(m-p),m-pivot-2,beta[pivot]-2,q-beta[pivot]};
                if(stat!=expected)fail("refinement statistic differs",beta,p,q);
                Disjoint g=erase_pivot(b);
                if(!disjoint_valid(g))fail("pivot deletion fails disjoint flags",beta,p,q);
                Boundary returned_pivot=add_pivot(g);
                if(returned_pivot.beta!=beta||returned_pivot.p!=p||returned_pivot.q!=q)
                    fail("add_pivot(erase_pivot(b)) differs",beta,p,q);
            }
        }while(next_permutation(beta.begin(),beta.end()));
        Perm gamma(n-3);iota(gamma.begin(),gamma.end(),1);
        int l=gamma.size();
        do {
            if(five_count(gamma))continue;
            for(int P=1;P<l;++P)for(int Q=1;P+Q<=l;++Q)
                for(int R=1;R<=P;++R)for(int T=1;T<=Q;++T) {
                    Disjoint g{gamma,P,Q,R,T};
                    if(!disjoint_valid(g))continue;
                    ++disjoints;
                    Boundary b=add_pivot(g);
                    if(!boundary_valid(b))fail("pivot insertion fails boundary class",gamma,P,Q);
                    Disjoint returned=erase_pivot(b);
                    if(returned.gamma!=gamma||returned.P!=P||returned.Q!=Q||returned.R!=R||returned.T!=T)
                        fail("erase_pivot(add_pivot(g)) differs",gamma,P,Q);
                }
        }while(next_permutation(gamma.begin(),gamma.end()));
        cout<<"n="<<n<<" forward_objects="<<halves<<" inverse_objects="<<boundaries
            <<" disjoint_objects="<<disjoints
            <<" all_object_round_trips=PASS spine=PASS northern=PASS statistics=PASS"<<endl;
    }
}
