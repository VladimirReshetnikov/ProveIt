#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,z;bool operator==(const A&a)const{return w==a.w&&d==a.d&&z==a.z;}};
struct C{int q,m;vector<tuple<int,int,int>>path;};
struct Test{C*c;vector<uint64_t>goals;bool ohalt;int q,h;};
const int R=7,F=97;A O[303][2],N[303][2];vector<int>Q;vector<C>cs[303];int kp,dr,sh;
uint64_t key(int q,int h,int m){return (uint64_t(q)<<21)|(uint64_t(h+16)<<15)|m;}
Test make(C&c){Test t{&c,{},false,c.q==dr?kp:c.q,c.q==dr?sh:0};for(auto[q,h,m]:c.path){t.ohalt|=q==254;t.goals.push_back(key(q==dr?kp:q,h+(q==dr?sh:0),m));}sort(t.goals.begin(),t.goals.end());return t;}
bool run(Test&t,vector<pair<int,int>>*trace=nullptr){int q=t.q,h=t.h,m=t.c->m;uint64_t seen[F];int sn=0;for(int k=0;k<F;k++){if(q==254||h< -R||h>R)return false;auto v=key(q,h,m);for(int j=0;j<sn;j++)if(seen[j]==v)return false;seen[sn++]=v;int b=(m>>(h+R))&1;if(trace)trace->push_back({q,b});auto a=N[q][b];m=(m&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;q=a.z;if(q==254)return t.ohalt;if(binary_search(t.goals.begin(),t.goals.end(),key(q,h,m)))return true;}return false;}
int main(int argc,char**argv){ifstream f(argv[1]);int n;f>>n;for(int i=0;i<n;i++){int q;f>>q;Q.push_back(q);for(int b=0;b<2;b++)f>>O[q][b].w>>O[q][b].d>>O[q][b].z;}int count;f>>count;for(int i=0;i<count;i++){int q,m;f>>q>>m;C c{q,m,{}};int x=q,h=0,t=m;for(int k=0;k<F;k++){if(x==254||h< -R||h>R)break;auto a=O[x][(t>>(h+R))&1];t=(t&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;x=a.z;c.path.emplace_back(x,h,t);}cs[q].push_back(move(c));}
// Put the extreme contexts first; subsequent failures become persistent witnesses.
for(int q:Q)if(cs[q].size()>1)swap(cs[q][1],cs[q].back());
ifstream spec(argv[2]);string tag;A ka[2];int idx=0,hits=0;long long tried=0,firstpass=0;auto begin=chrono::steady_clock::now();
while(spec>>tag>>kp>>dr>>sh>>ka[0].w>>ka[0].d>>ka[0].z>>ka[1].w>>ka[1].d>>ka[1].z){idx++;for(int q:Q)for(int b=0;b<2;b++){N[q][b]=O[q][b];if(N[q][b].z==dr){N[q][b].z=kp;N[q][b].d+=sh;}}N[kp][0]=ka[0];N[kp][1]=ka[1];
map<int,vector<Test>>cache;auto get=[&](int q)->vector<Test>&{if(!cache.count(q)){vector<Test>v;for(auto&c:cs[q])v.push_back(make(c));cache[q]=move(v);}return cache[q];};
vector<Test*> witnesses;vector<pair<int,int>>trace;
for(int q:{dr,kp}){for(auto&t:get(q))if(!run(t)){witnesses.push_back(&t);run(t,&trace);break;}if(!witnesses.empty())break;}
if(witnesses.empty()){cerr<<"BASEPASS "<<idx<<endl;continue;}
vector<pair<int,int>>rows;set<pair<int,int>>srows;for(auto r:trace)if(r.first!=kp&&r.first!=dr&&srows.insert(r).second)rows.push_back(r);
int loc=0;for(auto[p,b]:rows){A saved=N[p][b];for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:Q){if(z==dr)continue;A alt{w,d,z};if(alt==saved)continue;tried++;N[p][b]=alt;bool pass=true;for(Test*t:witnesses)if(!run(*t)){pass=false;break;}if(!pass)continue;firstpass++;
// The helper's other read branch can also reach the patched branch within the block, so check both.
for(int q:{p,dr,kp}){for(auto&t:get(q))if(!run(t)){pass=false;if(witnesses.size()<256&&find(witnesses.begin(),witnesses.end(),&t)==witnesses.end())witnesses.push_back(&t);break;}if(!pass)break;}
if(pass){hits++;loc++;cout<<"HIT "<<idx<<" "<<kp<<" "<<dr<<" "<<sh<<" "<<ka[0].w<<" "<<ka[0].d<<" "<<ka[0].z<<" "<<ka[1].w<<" "<<ka[1].d<<" "<<ka[1].z<<" "<<p<<" "<<b<<" "<<w<<" "<<d<<" "<<z<<endl;}}
N[p][b]=saved;}
cerr<<"SPEC "<<idx<<" rows "<<rows.size()<<" witnesses "<<witnesses.size()<<" tried "<<tried<<" partial "<<firstpass<<" hits "<<hits<<" time "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;
}
cerr<<"DONE "<<idx<<" "<<tried<<" "<<firstpass<<" "<<hits<<endl;
}
