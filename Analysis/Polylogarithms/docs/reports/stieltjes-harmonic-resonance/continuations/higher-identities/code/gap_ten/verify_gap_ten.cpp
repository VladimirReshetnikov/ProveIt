#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

// Exact, independently replayable finite-field certificate for half-gap 5.
// All polynomial products use radix-two NTTs in F_998244353.
// The mathematical certificate is the recurrence plus nonzero determinants;
// a checksum of its CSV is only an identifier, not a proof ingredient.
using namespace std;
using i64 = int64_t;
constexpr int MOD = 998244353, ROOT = 3, M = 5;

int addmod(int a, int b) { int s = a + b; return s >= MOD ? s-MOD : s; }
int submod(int a, int b) { int d = a-b; return d < 0 ? d+MOD : d; }
int mulmod(int a, int b) { return int(i64(a)*b % MOD); }
int powmod(int a, int n) {
    int r=1;
    while (n) { if(n&1) r=mulmod(r,a); a=mulmod(a,a); n>>=1; }
    return r;
}
int inverse(int a) {
    if (!a) throw runtime_error("zero denominator");
    return powmod(a,MOD-2);
}
void require(bool q, const string& msg) { if (!q) throw runtime_error(msg); }

void ntt(vector<int>& a, bool invert) {
    const int n=int(a.size());
    for(int i=1,j=0;i<n;++i) {
        int bit=n>>1;
        for(;j&bit;bit>>=1) j^=bit;
        j^=bit;
        if(i<j) swap(a[i],a[j]);
    }
    for(int len=2;len<=n;len<<=1) {
        int wlen=powmod(ROOT,(MOD-1)/len);
        if(invert) wlen=inverse(wlen);
        for(int i=0;i<n;i+=len) {
            int w=1;
            for(int j=0;j<len/2;++j) {
                int u=a[i+j],v=mulmod(a[i+j+len/2],w);
                a[i+j]=addmod(u,v);
                a[i+j+len/2]=submod(u,v);
                w=mulmod(w,wlen);
            }
        }
    }
    if(invert) { int iv=inverse(n); for(int& x:a) x=mulmod(x,iv); }
}
vector<int> multiply(const vector<int>& a,const vector<int>& b,int limit) {
    if(a.empty()||b.empty()||limit==0) return {};
    int sz=min(limit,int(a.size()+b.size()-1)),len=1;
    while(len<int(a.size()+b.size()-1)) len<<=1;
    vector<int> aa(len),bb(len);
    copy(a.begin(),a.end(),aa.begin()); copy(b.begin(),b.end(),bb.begin());
    ntt(aa,false); ntt(bb,false);
    for(int i=0;i<len;++i) aa[i]=mulmod(aa[i],bb[i]);
    ntt(aa,true); aa.resize(sz); return aa;
}
vector<int> reciprocal(const vector<int>& a,int n) {
    require(!a.empty()&&a[0],"noninvertible power series");
    vector<int> v{inverse(a[0])};
    while(int(v.size())<n) {
        int k=min(n,2*int(v.size()));
        vector<int> ap(a.begin(),a.begin()+min(k,int(a.size())));
        auto av=multiply(ap,v,k); av.resize(k);
        for(int& x:av) x=x?MOD-x:0;
        av[0]=addmod(av[0],2);
        v=multiply(v,av,k); v.resize(k);
    }
    return v;
}

vector<int> cotangent(int n) {
    vector<int> fact(2*n+2,1),ifact(2*n+2,1);
    for(int i=1;i<int(fact.size());++i) fact[i]=mulmod(fact[i-1],i);
    ifact.back()=inverse(fact.back());
    for(int i=int(ifact.size())-1;i>0;--i) ifact[i-1]=mulmod(ifact[i],i);
    vector<int> sine(n+1),cosine(n+1);
    int scale=1, minus_quarter=submod(0,inverse(4));
    for(int k=0;k<=n;++k) {
        sine[k]=mulmod(scale,ifact[2*k+1]);
        cosine[k]=mulmod(scale,ifact[2*k]);
        scale=mulmod(scale,minus_quarter);
    }
    auto invs=reciprocal(sine,n+1);
    auto unit=multiply(sine,invs,n+1);
    require(unit[0]==1,"reciprocal constant");
    for(int k=1;k<=n;++k) require(unit[k]==0,"reciprocal product");
    auto quotient=multiply(cosine,invs,n+1);
    vector<int> beta(n+1); beta[0]=0;
    for(int k=1;k<=n;++k) beta[k]=submod(0,addmod(quotient[k],quotient[k]));
    require(beta[1]==inverse(6),"cotangent first coefficient");
    // Independent Riccati recurrence, verified simultaneously by convolution.
    auto square=multiply(beta,beta,n+1);
    for(int k=2;k<=n;++k)
        require(mulmod(2*(2*k+1),beta[k])==square[k],"cotangent Riccati identity");
    return beta;
}

struct Fundamental {
    int count, padded;
    const vector<int>& beta;
    vector<int> aa,bb,invd;
    array<vector<int>,M> rr,leftsum,rightsum;
    vector<vector<int>> kernel;

    Fundamental(int count_,const vector<int>& beta_):count(count_),beta(beta_) {
        padded=1;while(padded<count)padded<<=1;
        aa.assign(count,0);bb.assign(count,0);invd.assign(count,0);
        for(int j=0;j<M;++j) {
            rr[j].assign(count,0);leftsum[j].assign(count,0);rightsum[j].assign(count,0);
        }
        for(int s=M+1;s<count;++s) {
            int a=1,b=1;
            for(int k=0;k<2*M;++k) {a=mulmod(a,2*s-k);b=mulmod(b,2*s-1-k);}
            aa[s]=a;bb[s]=b;invd[s]=inverse(addmod(addmod(a,b),addmod(a,b)));
        }
        int log=0;while((1<<log)<padded)++log;
        kernel.resize(log+1);
        for(int lev=6;lev<=log;++lev) {
            int len=1<<lev;kernel[lev].assign(len,0);
            for(int k=1;k<len&&k<int(beta.size());++k)kernel[lev][k]=beta[k];
            ntt(kernel[lev],false);
        }
    }
    void leaf(int s) {
        if(s>=1&&s<=M) {for(int j=0;j<M;++j)rr[j][s]=(s==j+1);}
        else if(s>M) {
            for(int j=0;j<M;++j)
                rr[j][s]=mulmod(addmod(mulmod(bb[s],leftsum[j][s]),rightsum[j][s]),invd[s]);
        }
    }
    void solve(int l,int r,int lev) {
        if(l>=count)return;
        int end=min(r,count);
        if(r-l<=32) {
            for(int s=l;s<end;++s) {
                leaf(s);
                for(int t=s+1;t<end;++t) {
                    int w=beta[t-s],wa=mulmod(w,aa[s]);
                    for(int j=0;j<M;++j) {
                        leftsum[j][t]=addmod(leftsum[j][t],mulmod(w,rr[j][s]));
                        rightsum[j][t]=addmod(rightsum[j][t],mulmod(wa,rr[j][s]));
                    }
                }
            }
            return;
        }
        int mid=(l+r)/2,len=r-l;
        solve(l,mid,lev-1);
        if(mid>=count)return;
        vector<int> work(len);
        // Cyclic length-len convolution has no wrap into the right half:
        // left input has support [0,len/2), so wraps land below len/2.
        for(int j=0;j<M;++j)for(int weighted=0;weighted<2;++weighted) {
            fill(work.begin(),work.end(),0);
            for(int s=l;s<mid;++s)
                work[s-l]=weighted?mulmod(aa[s],rr[j][s]):rr[j][s];
            ntt(work,false);
            for(int k=0;k<len;++k)work[k]=mulmod(work[k],kernel[lev][k]);
            ntt(work,true);
            auto& target=weighted?rightsum[j]:leftsum[j];
            for(int s=mid;s<end;++s)target[s]=addmod(target[s],work[s-l]);
        }
        solve(mid,r,lev-1);
    }
    void run() {
        int lev=0;while((1<<lev)<padded)++lev;
        solve(0,padded,lev);
        // Verify every recurrence through separate non-causal products.
        for(int j=0;j<M;++j) {
            auto unweighted=multiply(beta,rr[j],count);
            vector<int> arr(count);
            for(int s=0;s<count;++s)arr[s]=mulmod(aa[s],rr[j][s]);
            auto weighted=multiply(beta,arr,count);
            for(int s=M+1;s<count;++s)
                require(rr[j][s]==mulmod(addmod(mulmod(bb[s],unweighted[s]),weighted[s]),invd[s]),
                        "full fundamental recurrence verification");
        }
    }
    int determinant(int b) const {
        array<array<int,M>,M> v{};
        for(int i=0;i<M;++i)for(int j=0;j<M;++j)v[i][j]=rr[j][b+i+1];
        int det=1;
        for(int k=0;k<M;++k) {
            int p=k;while(p<M&&!v[p][k])++p;
            if(p==M)return 0;
            if(p!=k){swap(v[p],v[k]);det=submod(0,det);}
            det=mulmod(det,v[k][k]);int inv=inverse(v[k][k]);
            for(int i=k+1;i<M;++i) {
                int f=mulmod(v[i][k],inv);
                for(int j=k+1;j<M;++j)v[i][j]=submod(v[i][j],mulmod(f,v[k][j]));
            }
        }
        return det;
    }
};

bool is_prime_trial(int p) {
    if(p<2||p%2==0)return p==2;
    for(int d=3;i64(d)*d<=p;d+=2)if(p%d==0)return false;
    return true;
}
int main(int argc,char** argv) {
    try {
        int threshold=argc>1?stoi(argv[1]):73728;
        string csv=argc>2?argv[2]:"gap_ten_certificate.csv";
        require(threshold>M+1,"invalid threshold");
        require(is_prime_trial(MOD),"prime certificate");
        require(powmod(ROOT,(MOD-1)/2)!=1 && powmod(ROOT,(MOD-1)/7)!=1
                && powmod(ROOT,(MOD-1)/17)!=1,"primitive root certificate");
        int nmax=threshold+M-1;
        require(4*nmax+2<MOD,"denominator range");
        cout<<"Certified prime and primitive root. Computing cotangent coefficients through "<<nmax-1<<endl;
        auto beta=cotangent(nmax-1); beta.resize(nmax+1,0);
        cout<<"Cotangent identities verified. Computing five fundamental columns through "<<nmax<<endl;
        Fundamental f(nmax+1,beta);f.run();
        cout<<"All fundamental recurrences independently verified. Checking determinants."<<endl;
        ofstream out(csv);require(bool(out),"cannot write certificate");out<<"b,det_mod_998244353\n";
        int nonzero=0,zero=0;
        for(int b=M+1;b<threshold;++b) {
            int d=f.determinant(b);out<<b<<","<<d<<"\n";
            if(d)++nonzero;else{++zero;cerr<<"Zero residue at b="<<b<<endl;}
        }
        out.close();
        cout<<"half_gap="<<M<<" threshold="<<threshold<<" prime="<<MOD
            <<" nonzero="<<nonzero<<" zero="<<zero<<" file="<<csv<<endl;
        return zero?2:0;
    }catch(const exception& e){cerr<<e.what()<<endl;return 1;}
}
