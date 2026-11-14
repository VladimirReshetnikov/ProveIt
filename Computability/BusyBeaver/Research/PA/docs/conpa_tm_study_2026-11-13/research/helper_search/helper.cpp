#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;
// Actions: 4*q + 2*write + (direction==R).
constexpr int N=197, A=4*N, R=4, LIMIT=31;
using Bits=bitset<A>;
struct Row { int w,d,q; };
array<array<Row,2>,N> m;
array<vector<int>,N> ctx;
array<bool,N> allowed;
struct Rules { Bits v[2]; };
array<array<array<Rules,4>,2>,N> rules;
Row decode(int a) { return { (a%4)/2, (a%2)?1:-1, a/4 }; }
int encode(Row r) { return 4*r.q+2*r.w+(r.d==1); }
bool route(int q,int b,int first,int a,int t) {
    Row old=m[q][b], h=decode(a);
    int initial=t, w=first/2,d=(first%2)?1:-1;
    int want=(initial&~(1<<R))|(old.w<<R), target=old.q, pos=R+d;
    t=(t&~(1<<R))|(w<<R);
    t=(t&~(1<<pos))|(h.w<<pos); pos+=h.d;
    int s=h.q;
    for(int n=2;n<=LIMIT;n++) {
        if(pos==R+old.d && s==target && t==want) return true;
        if(pos<0||pos>2*R||s==q||s>=196) return false;
        Row r=m[s][(t>>pos)&1];
        t=(t&~(1<<pos))|(r.w<<pos); pos+=r.d; s=r.q;
    }
    return false;
}
struct Pair { int q,p,a0,a1; Bits v0,v1; };
int main(int argc,char**argv) {
    if(argc!=4) return 2;
    ifstream tab(argv[1]);int q,b,w,n;char d;
    while(tab>>q>>b>>w>>d>>n)m[q][b]={w,d=='R'?1:-1,n};
    ifstream con(argv[2]);int count,ok,t;
    while(con>>q>>ok>>count) {allowed[q]=ok;while(count--){con>>t;ctx[q].push_back(t);}}
    for(int q=0;q<196;q++)if(allowed[q])for(int b=0;b<2;b++)for(int f=0;f<4;f++) {
        for(int c=0;c<2;c++)rules[q][b][f].v[c].set();
        int pos=R+((f%2)?1:-1);
        for(int t:ctx[q])if(((t>>R)&1)==b) {
            int c=(t>>pos)&1;
            auto &v=rules[q][b][f].v[c];
            for(int a=0;a<A;a++)if(v[a] && !route(q,b,f,a,t))v.reset(a);
        }
    }
    Bits full;full.set();vector<Pair> pairs;
    for(int q=0;q<196;q++)if(allowed[q])for(int p=q+1;p<196;p++)if(allowed[p]) {
        vector<pair<int,Rules>> choices[2];
        for(int b=0;b<2;b++) {
            if(encode(m[q][b])==encode(m[p][b]))choices[b].push_back({-1,{full,full}});
            for(int f=0;f<4;f++) {
                Rules r;for(int c=0;c<2;c++)r.v[c]=rules[q][b][f].v[c]&rules[p][b][f].v[c];
                if(r.v[0].any()&&r.v[1].any())choices[b].push_back({f,r});
            }
        }
        for(auto &a:choices[0])for(auto &b:choices[1]) {
            Bits v0=a.second.v[0]&b.second.v[0],v1=a.second.v[1]&b.second.v[1];
            if(v0.any()&&v1.any())pairs.push_back({q,p,a.first,b.first,v0,v1});
        }
    }
    cerr<<"merge constraints "<<pairs.size()<<"\n";
    ofstream out(argv[3]);long combinations=0,candidates=0;
    for(size_t i=0;i<pairs.size();i++)for(size_t j=i+1;j<pairs.size();j++) {
        auto a=pairs[i],b=pairs[j];
        bool disjoint=a.q!=b.q&&a.q!=b.p&&a.p!=b.q&&a.p!=b.p;
        bool triple=a.q==b.q&&a.p!=b.p&&a.a0==b.a0&&a.a1==b.a1;
        if(!disjoint&&!triple)continue;
        Bits v0=a.v0&b.v0,v1=a.v1&b.v1;
        if(v0.none()||v1.none())continue;
        combinations++;
        for(int h0=0;h0<A;h0++)if(v0[h0])for(int h1=0;h1<A;h1++)if(v1[h1]) {
            int u=h0/4,v=h1/4;
            if(u==a.q||u==a.p||u==b.q||u==b.p||v==a.q||v==a.p||v==b.q||v==b.p)continue;
            out<<a.q<<" "<<a.p<<" "<<a.a0<<" "<<a.a1<<" "<<b.q<<" "<<b.p<<" "<<b.a0<<" "<<b.a1<<" "<<h0<<" "<<h1<<"\n";candidates++;
        }
    }
    cerr<<"compatible pairs "<<combinations<<" candidates "<<candidates<<"\n";
    ofstream detail(string(argv[3])+".constraints");
    for(auto &p:pairs) {detail<<p.q<<" "<<p.p<<" "<<p.a0<<" "<<p.a1;for(int c=0;c<2;c++){detail<<" |";auto v=c?p.v1:p.v0;for(int a=0;a<A;a++)if(v[a])detail<<" "<<a;}detail<<"\n";}
}
