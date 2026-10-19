// Joint two-helper state-fold discovery. Unlike neutral helper-domain searches,
// helper edits need not individually simulate the baseline table.
// Any empirical-profile output requires an independent all-tape verification.
// 2026-10-19. Standalone C++17 implementation for the ProveIt ZFC237 study.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <queue>
#include <set>
#include <sstream>
#include <tuple>
#include <vector>
using namespace std;
struct Row {int w,d,z;bool operator==(Row const& a)const{return tie(w,d,z)==tie(a.w,a.d,a.z);}};
struct Cfg {int q,h,t;};
struct Case {int q,b,t;vector<Cfg> goals;};
struct Patch {int e;Row a;};
array<array<Row,2>,256> T;vector<int> states, inv[256];
vector<Case> pre[512];int L=5,R=5,H=25,W,N,mask,p,q, common;
Row ret[2];Patch hs[2];int nh=0;
long long sims=0,rows=0,firsts=0,seconds=0,repairs=0,found=0;
int mp(int s){return s==q?p:s;}
vector<int> edges;Case const* failure=nullptr;
bool test(Case const& c,bool save=false){
 ++sims;int s=mp(c.q),h=0,t=c.t;vector<int> path;
 for(int k=0;k<H;k++){
  if(h < -L || h>R || s==254)break;
  int b=(t>>(h+L))&1,e=2*s+b;Row a=T[s][b];
  if(s==p)a=ret[b];
  else {if(save)path.push_back(e);for(int j=0;j<nh;j++)if(hs[j].e==e)a=hs[j].a;}
  t=(t&~(1<<(h+L)))|(a.w<<(h+L));h+=a.d;s=mp(a.z);
  for(auto const&g:c.goals)if(s==mp(g.q)&&h==g.h&&t==g.t)return true;
 }
 if(save){sort(path.begin(),path.end());path.erase(unique(path.begin(),path.end()),path.end());edges=move(path);failure=&c;}
 return false;
}
bool group(vector<Case const*>const&v,bool save=true){for(auto c:v)if(!test(*c,save))return false;return true;}
void add(vector<Case const*>& v,int e){for(auto const&c:pre[e])v.push_back(&c);}
void emit(){
 ++found;cout<<"CANDIDATE "<<p<<' '<<q<<" RET ";for(auto a:ret)cout<<a.w<<' '<<a.d<<' '<<a.z<<"; ";
 cout<<"HELPERS ";for(int i=0;i<nh;i++){auto a=hs[i].a;cout<<hs[i].e/2<<' '<<hs[i].e%2<<' '<<a.w<<' '<<a.d<<' '<<a.z<<"; ";}cout<<endl;
}
int main(int argc,char**argv){
 if(argc<2){cerr<<"usage: coupled_helpers TABLE [L R steps profile-or-- first-pair last-pair]"<<endl;return 2;}
 if(argc>2)L=stoi(argv[2]);if(argc>3)R=stoi(argv[3]);if(argc>4)H=stoi(argv[4]);
 int begin=argc>6?stoi(argv[6]):0,end=argc>7?stoi(argv[7]):10000;
 W=L+R+1;N=1<<W;mask=N-1;
 ifstream f(argv[1]);string line;set<int> exist;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int s,b,w,z;char d;ss>>s>>b>>w>>d>>z;T[s][b]={w,d=='R'?1:-1,z};exist.insert(s);}
 states.assign(exist.begin(),exist.end());
 if(argc>5&&string(argv[5])!="-"){ifstream f2(argv[5]);int s,t;while(f2>>s>>t)inv[s].push_back(t);}
 else {
  vector<vector<bool>> seen(256,vector<bool>(N));queue<pair<int,int>>todo;
  for(int t=0;t<N;t++){seen[95][t]=true;todo.push({95,t});}
  while(!todo.empty()){
   auto [s,t]=todo.front();todo.pop();inv[s].push_back(t);if(s==254)continue;
   auto a=T[s][(t>>L)&1];int u=(t&~(1<<L))|(a.w<<L),u0,u1;
   if(a.d==1){u0=u>>1;u1=u0|(1<<(W-1));}else{u0=(u<<1)&mask;u1=u0|1;}
   for(int v:{u0,u1})if(!seen[a.z][v]){seen[a.z][v]=true;todo.push({a.z,v});}
  }
 }
 long long contexts=0;
 for(int s:states){
  sort(inv[s].begin(),inv[s].end(),[&](int x,int y){return (x*101&mask)<(y*101&mask);});
  for(int t:inv[s]){
   int b=t>>L&1;Case c{s,b,t,{}};int z=s,h=0,u=t;
   for(int k=0;k<H;k++){
    if(z==254||h < -L||h>R)break;
    auto a=T[z][(u>>(h+L))&1];u=(u&~(1<<(h+L)))|(a.w<<(h+L));h+=a.d;z=a.z;c.goals.push_back({z,h,u});
   }
   pre[2*s+b].push_back(move(c));contexts++;
  }
 }
 vector<Row> domain;
 for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:states)domain.push_back({w,d,z});
 auto start=chrono::steady_clock::now();int ix=-1;
 cerr<<"BEGIN contexts "<<contexts<<" radius "<<L<<' '<<R<<" horizon "<<H<<" pairrange "<<begin<<' '<<end<<endl;
 for(int pp:states)for(int qq:states)if(pp<qq){
  common=-1;for(int b=0;b<2;b++)if(T[pp][b]==T[qq][b])common=b;if(common<0)continue;
  ++ix;if(ix<begin||ix>=end)continue;p=pp;q=qq;int diff=1-common;
  vector<Case const*> base;add(base,2*p+diff);add(base,2*q+diff);
  stable_sort(base.begin(),base.end(),[&](auto x,auto y){return (x->t*101&mask)<(y->t*101&mask);});
  add(base,2*p+common);add(base,2*q+common);ret[common]=T[p][common];
  for(auto rr:domain)if(rr.z!=q){
   ret[diff]=rr;++rows;nh=0;if(group(base)){emit();continue;}
   auto initialedges=edges;auto initialfail=failure;
   for(int e:initialedges)if(e/2!=p&&e/2!=q){
    hs[0].e=e;nh=1;
    for(auto a:domain)if(a.z!=q&&!(a==T[e/2][e%2])){
     hs[0].a=a;++firsts;
     if(!test(*initialfail))continue;
     if(!group(base))continue;
     ++repairs;vector<Case const*> stage=base;add(stage,e);
     if(group(stage)){emit();continue;}
     auto moreedges=edges;auto nextfail=failure;
     for(int e2:moreedges)if(e2/2!=p&&e2/2!=q&&e2!=e){
      hs[1].e=e2;nh=2;
      for(auto a2:domain)if(a2.z!=q&&!(a2==T[e2/2][e2%2])){
       hs[1].a=a2;++seconds;
       if(!test(*nextfail)||!test(*initialfail))continue;
       if(!group(stage))continue;
       bool good=true;for(auto const&c:pre[e2])if(!test(c)){good=false;break;}
       if(good)emit();
      }
      nh=1;
     }
    }
    nh=0;
   }
  }
  cerr<<"PAIR "<<ix<<' '<<p<<' '<<q<<" rows "<<rows<<" first "<<firsts<<" repaired "<<repairs<<" second "<<seconds<<" sims "<<sims<<" found "<<found<<" sec "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"FINISHED contexts "<<contexts<<" pairs "<<ix+1<<" rows "<<rows<<" first "<<firsts<<" repaired "<<repairs<<" second "<<seconds<<" sims "<<sims<<" candidates "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
