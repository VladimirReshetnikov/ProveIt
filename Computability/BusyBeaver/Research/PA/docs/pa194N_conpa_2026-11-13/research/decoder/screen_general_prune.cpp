#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <unordered_map>
#include <vector>
using namespace std;
struct A{int w,d,n;bool operator==(A const&v)const{return w==v.w&&d==v.d&&n==v.n;}};
static A rows[2500][2];static bool fixedstate[2500];
static vector<int> base;
static const int vars[3]={98,12,166};
static const int perms[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
uint32_t ac(A a){return uint32_t((a.n+2)*4+a.w*2+a.d);}
uint64_t key(int a,int b){return(uint64_t(uint32_t(a))<<32)|uint32_t(b);}
struct T{int op,a,b,c;};
struct Provider{int h,u0,u1;};
struct Result{int n,fold,effective;};
static bool use_compatible=false;
struct Op{int a,b;array<vector<A>,2>choices;};
struct Choice{int a,b;array<A,2>actions;};
int maximum_compatible(vector<Op>const&ops,int bound,int shape_count){
 int aliases[2500]={};bool keep[2500]={},used[2500]={};A patched[2500][2];vector<Choice>chosen;
 auto alias=[&](int q){return q>=0&&q<2500&&aliases[q]?aliases[q]:q;};
 auto valid=[&](){
  for(auto c:chosen)for(int context=0;context<2;context++)for(int bit=0;bit<2;bit++){
   int old=context?c.b:c.a;A target=rows[old][bit];int targetq=alias(target.n),targeth=target.d?1:-1;
   int tape[2]={context,bit};int q=c.b,h=0;bool pass=false;
   for(int step=0;step<20;step++){
    if(step&&h==targeth&&q==targetq&&tape[0]==context&&tape[1]==target.w){pass=true;break;}
    if(h< -1||h>0||q<0||q>=2500||aliases[q]||(!fixedstate[q]&&!(q>=2000&&q<2000+shape_count)))break;
    A a=keep[q]?patched[q][tape[h+1]]:rows[q][tape[h+1]];
    tape[h+1]=a.w;h+=a.d?1:-1;q=alias(a.n);
   }
   if(!pass)return false;
  }
  return true;
 };
 for(int goal=bound;goal>0;goal--){
  function<bool(int)>dfs=[&](int i){
   if(int(chosen.size())==goal)return valid();
   if(i==int(ops.size())||int(chosen.size()+ops.size())-i<goal)return false;
   auto const&o=ops[i];
   if(!used[o.a]&&!used[o.b]){
    used[o.a]=used[o.b]=true;aliases[o.a]=o.b;keep[o.b]=true;
    for(A z:o.choices[0])for(A u:o.choices[1]){
     patched[o.b][0]=z;patched[o.b][1]=u;chosen.push_back({o.a,o.b,{z,u}});
     if(valid()&&dfs(i+1))return true;
     chosen.pop_back();
    }
    used[o.a]=used[o.b]=false;aliases[o.a]=0;keep[o.b]=false;
   }
   return dfs(i+1);
  };
  if(dfs(0))return goal;
 }
 return 0;
}
Result calc(vector<T>const&ns,int root,array<int,6>ps){
 unordered_map<uint64_t,int> intern;intern.reserve(128);
 vector<int> value(ns.size());int n=0;
 for(int i=0;i<int(ns.size());i++){
  auto t=ns[i];
  if(!t.op){value[i]=(t.b>=0)?vars[perms[ps[t.b]][t.c]]:t.a;continue;}
  int l=value[t.a],r=value[t.b];
  static const map<pair<int,int>,int> freepairs={{{11,38},312},{{14,13},8},{{14,138},127},{{16,51},51},{{19,20},12},{{19,114},98},{{19,179},166},{{21,47},31},{{21,126},107},{{21,141},128},{{22,55},55},{{25,48},48},{{27,110},95},{{28,20},38},{{28,29},19},{{30,31},20},{{30,70},137},{{32,33},33},{{33,22},22},{{36,25},25},{{39,73},123},{{41,42},28},{{41,63},70},{{43,44},29},{{45,46},30},{{45,103},301},{{48,32},32},{{51,36},36},{{53,310},84},{{55,60},60},{{56,57},43},{{58,59},44},{{58,125},106},{{61,61},99},{{61,62},46},{{62,42},109},{{62,72},59},{{62,138},124},{{62,139},125},{{68,69},53},{{70,71},58},{{72,59},105},{{74,64},64},{{75,84},75},{{77,98},164},{{77,122},196},{{77,254},68},{{82,81},91},{{82,83},73},{{87,88},77},{{92,90},213},{{95,111},188},{{99,99},190},{{101,100},96},{{104,128},111},{{104,185},92},{{105,106},90},{{107,98},185},{{108,109},93},{{109,130},197},{{122,103},88},{{123,124},104},{{127,8},110},{{130,107},114},{{174,164},100},{{188,312},214},{{194,42},26},{{194,128},179},{{196,217},221},{{197,196},217},{{213,28},174},{{214,62},310},{{301,21},87}};
  auto fi=freepairs.find({l,r}); if(fi!=freepairs.end()){value[i]=fi->second;continue;}
  auto k=key(l,r);auto it=intern.find(k);
  if(it!=intern.end()){value[i]=it->second;continue;}
  int q=2000+n++;intern.emplace(k,q);value[i]=q;
  rows[q][0]=(l==-1)?A{0,0,302}:A{0,1,l};
  rows[q][1]=(r==-1)?A{0,0,302}:A{1,1,r};
 }
 rows[101][1]={1,1,value[root]};
 unsigned incoming[2500]={};
 auto inc=[&](int q){for(int b=0;b<2;b++){auto a=rows[q][b];if(a.n>=0&&a.n<2500)incoming[a.n]|=a.d?(1u<<a.w):4u;}};
 for(auto q:base)inc(q);for(int j=0;j<n;j++)inc(2000+j);
 incoming[74]|=4;
 unordered_map<uint64_t,vector<Provider>> providers[2];providers[0].reserve(256);providers[1].reserve(256);
 auto exists=[&](int q){return q>=0&&q<2500&&(fixedstate[q]||(q>=2000&&q<2000+n));};
 auto provide=[&](int h){auto z=rows[h][0],o=rows[h][1];if(z.w||o.w!=1||!z.d||!o.d)return;
  if(!exists(z.n)||!exists(o.n))return;
  for(int b=0;b<2;b++)providers[b][key(ac(rows[z.n][b]),ac(rows[o.n][b]))].push_back({h,z.n,o.n});};
 for(auto q:base)provide(q);for(int j=0;j<n;j++)provide(2000+j);
 vector<int> left,right;
 auto endpoint=[&](int q){if(incoming[q]==1)left.push_back(q);if(incoming[q]==2)right.push_back(q);};
 for(int q:base) endpoint(q);for(int j=0;j<n;j++)endpoint(2000+j);
 vector<vector<int>> edges(2500);vector<Op>ops;
 for(auto a:left)for(auto b:right){bool possible=true;array<vector<A>,2>choices;
  for(int bit=0;bit<2;bit++){
   if(rows[a][bit]==rows[b][bit]){if(use_compatible)choices[bit].push_back(rows[a][bit]);continue;}
   auto it=providers[bit].find(key(ac(rows[a][bit]),ac(rows[b][bit])));bool found=false;
   if(it!=providers[bit].end())for(auto p:it->second){if(p.h!=a&&p.h!=b&&p.u0!=a&&p.u0!=b&&p.u1!=a&&p.u1!=b){found=true;if(use_compatible)choices[bit].push_back({bit,0,p.h});else break;}}
   if(!found){possible=false;break;}
  }
  if(possible){edges[a].push_back(b);if(use_compatible)ops.push_back({a,b,choices});}
 }
 vector<int> match(2500,-1);int fold=0;
 function<bool(int,vector<bool>&)>augment=[&](int a,vector<bool>&seen){for(int b:edges[a]){if(seen[b])continue;seen[b]=true;if(match[b]==-1||augment(match[b],seen)){match[b]=a;return true;}}return false;};
 for(auto a:left){vector<bool>seen(2500);if(augment(a,seen))fold++;}
 if(use_compatible&&n-fold<=64)fold=maximum_compatible(ops,fold,n);
 return {n,fold,n-fold};
}
#ifndef PARAMETER_SCREEN_NO_MAIN
int main(int argc,char**argv){
 if(argc<3){cerr<<"screen templates.txt output-prefix [max-templates] [max-combos]\n";return 2;}
 if(argc>5)use_compatible=true;
 ifstream in(argv[1]);string pref=argv[2];ofstream hit(pref+".hits"),bestout(pref+".best"),audit(pref+".audit"),seeds(pref+".seeds");
 int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 int nt;in>>nt;int maxT=argc>3?atoi(argv[3]):nt;int maxC=argc>4?atoi(argv[4]):46656;auto start=chrono::steady_clock::now();int global=999;long long count=0,hits=0;
 for(int ti=0;ti<nt;ti++){
  int tid,nn,root;in>>tid>>nn>>root;vector<T>ns(nn);for(auto &x:ns)in>>x.op>>x.a>>x.b>>x.c;
  if(ti>=maxT)continue;int best=999;long long th=0;
  for(int k=0;k<maxC;k++){
   array<int,6>p;int x=k;for(int h=0;h<6;h++){p[h]=x%6;x/=6;}
   auto v=calc(ns,root,p);count++;
   if(k<6){audit<<tid<<' '<<k<<' '<<v.n<<' '<<v.fold<<' '<<v.effective<<'\n';}
   if(v.effective<best){best=v.effective;bestout<<tid<<' '<<k<<' '<<v.n<<' '<<v.fold<<' '<<v.effective<<'\n';bestout.flush();}
   if(v.effective<global){global=v.effective;cout<<"BEST "<<tid<<' '<<k<<" raw "<<v.n<<" folds "<<v.fold<<" score "<<v.effective<<endl;}
   if(v.effective<=61){hit<<tid<<' '<<k<<' '<<v.n<<' '<<v.fold<<' '<<v.effective<<'\n';hit.flush();hits++;th++;}
   if(v.effective<=63){seeds<<tid<<' '<<k<<' '<<v.n<<' '<<v.fold<<' '<<v.effective<<'\n';}
  }
  seeds.flush();double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();cout<<"TEMPLATE "<<tid<<" best "<<best<<" hits "<<th<<" cases "<<count<<" seconds "<<elapsed<<endl;
 }
 cout<<"DONE cases "<<count<<" hits "<<hits<<" best "<<global<<endl;
}
#endif
