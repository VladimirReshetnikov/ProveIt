#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <unordered_map>
#include <vector>
using namespace std;
struct Attr {int h,l,m,mi,inc;};
struct Meta {array<int,6> order{0,1,2,3,4,5},perm{0,0,0,0,0,0},flip{0,0,0,0,0,0};int gate=0;};
struct Stat {int eff,n,fold,pen;};
int nt,nw,np,nrows,stamp=0,look[262144],stamps[262144],termstate[32],pairinc,fourinc;
int preact[4096][2],acts[4096][2],incoming[4096];
vector<int> fixedstates, prefix,suffix,gates[2],hv[6][6][2];
vector<pair<int,int>> shape;
Attr termattrs[32],attrs[512];
int stateid[512],leftid[512],rightid[512],ids[512],ncanon;
vector<int> dyn;
vector<pair<int,int>> canonical;
mt19937_64 rng(731992600197);
int ai(int w,int d,int n){return 4*n+2*d+w;}
vector<int> readv(istream&f){int n;f>>n;vector<int>x(n);for(auto&v:x)f>>v;return x;}
void init(char*filename){ifstream f(filename);f>>nt>>nw>>np>>nrows;for(int i=0;i<nt;++i)f>>termstate[i]>>termattrs[i].h>>termattrs[i].l>>termattrs[i].m>>termattrs[i].mi>>termattrs[i].inc;
fill(&preact[0][0],&preact[0][0]+8192,-1);
for(int i=0;i<nrows;++i){int q,b,w,d,n;f>>q>>b>>w>>d>>n;preact[q][b]=ai(w,d,n);}
for(int q=0;q<4096;++q)if(preact[q][0]>=0)fixedstates.push_back(q);
for(int i=0;i<np;++i){int a,b;f>>a>>b;shape.push_back({a,b});}
prefix=readv(f);suffix=readv(f);gates[0]=readv(f);gates[1]=readv(f);
for(auto&h:hv)for(auto&p:h)for(auto&x:p)x=readv(f);
}
vector<int> word(const Meta&m){vector<int>w=prefix;for(int j:m.order){auto&h=hv[j][m.perm[j]][m.flip[j]];w.insert(w.end(),h.begin(),h.end());}w.insert(w.end(),gates[m.gate].begin(),gates[m.gate].end());w.insert(w.end(),suffix.begin(),suffix.end());return w;}
Attr join(Attr a,Attr b){return{1+max(a.h,b.h),1+a.l,max({1+a.l,a.m,b.m}),max({a.mi,b.mi,a.inc?1+a.l:0}),a.inc};}
int intern(int a,int b){int key=a*512+b;if(stamps[key]==stamp)return look[key];int id=ncanon++;stamps[key]=stamp;look[key]=id;leftid[id]=a;rightid[id]=b;attrs[id]=join(attrs[a],attrs[b]);stateid[id]=2000+id; if(a==3&&b==3){stateid[id]=99;pairinc=id;}else if(a==pairinc&&b==pairinc)stateid[id]=190;else dyn.push_back(id);return id;}
struct Prov{int h,u,v;};
using ProvMap=unordered_map<uint64_t,vector<Prov>>;
uint64_t keyof(int a,int b){return (uint64_t(uint32_t(a))<<32)|uint32_t(b);}

struct Opp {int a,b; vector<int>opts[2];};
vector<Opp> candidates;
int aliases[4096],changes[4096][2];
struct Chosen {int a,b,x,y;};
vector<Chosen> chosen;
bool compatible(){
 fill(aliases,aliases+4096,-1);fill(&changes[0][0],&changes[0][0]+8192,-1);
 for(auto c:chosen){aliases[c.a]=c.b;changes[c.b][0]=c.x;changes[c.b][1]=c.y;}
 auto alias=[](int q){return aliases[q]>=0?aliases[q]:q;};
 for(auto c:chosen)for(int hist=0;hist<2;++hist)for(int bit=0;bit<2;++bit){
  int q=hist?c.b:c.a,action=acts[q][bit];int goal=alias(action>>2),goalpos=(action&2)?1:-1,mask=hist+2*bit,want=hist+2*(action&1);int now=c.b,pos=0;bool pass=false;
  for(int step=0;step<20;++step){
   if(step&&pos==goalpos&&now==goal&&mask==want){pass=true;break;}
   if(pos < -1||pos>0)break;
   int rb=(mask>>(pos+1))&1;int a=changes[now][rb]>=0?changes[now][rb]:acts[now][rb];if(a<0)break;
   if(a&1)mask|=1<<(pos+1);else mask&=~(1<<(pos+1));pos+=(a&2)?1:-1;now=alias(a>>2);
  }
  if(!pass)return false;
 }
 return true;
}
int actualfolds(int upper){
 bool used[4096]={};
 for(int target=upper;target>0;--target){chosen.clear();
  auto dfs=[&](auto&&self,int i)->bool{
   if(int(chosen.size())==target)return compatible();
   if(i==int(candidates.size())||int(chosen.size())+int(candidates.size())-i<target)return false;
   auto &c=candidates[i];if(!used[c.a]&&!used[c.b]){
    used[c.a]=used[c.b]=true;
    for(int x:c.opts[0])for(int y:c.opts[1]){chosen.push_back({c.a,c.b,x,y});if(self(self,i+1))return true;chosen.pop_back();}
    used[c.a]=used[c.b]=false;
   }
   return self(self,i+1);
  };
  if(dfs(dfs,0))return target;
 }
 return 0;
}
vector<pair<int,int>> edgepairs;
Stat score(const Meta&m,bool extra=false){
++stamp;ncanon=nt;pairinc=-1;dyn.clear();edgepairs.clear();candidates.clear();
for(int i=0;i<nt;++i){stateid[i]=termstate[i];attrs[i]=termattrs[i];}
auto w=word(m);if(int(w.size())!=nw){cerr<<"size";exit(2);}copy(w.begin(),w.end(),ids);
for(int j=0;j<np;++j)ids[nw+j]=intern(ids[shape[j].first],ids[shape[j].second]);
int rootid=ids[nw+np-1];Attr at=attrs[rootid];int pen=20*(max(0,at.m-6)+max(0,at.mi-5))+max(0,at.h-38);
for(int j=0;j<np;++j){int a=ids[shape[j].first],b=ids[shape[j].second]; if(a==8||b==4)pen+=50;}
int n=dyn.size();
// Most variants cannot compete; skip expensive provider matching outside the useful band.
if(n>76)return{n,n,0,pen};
copy(&preact[0][0],&preact[0][0]+8192,&acts[0][0]);fill(incoming,incoming+4096,0);
vector<int>states=fixedstates;
for(int id:dyn){int q=stateid[id];states.push_back(q);int ch[2]={leftid[id],rightid[id]};for(int b=0;b<2;++b){int s=stateid[ch[b]];acts[q][b]=s==-1?ai(0,0,302):ai(b,1,s);}}
acts[101][1]=ai(1,1,stateid[rootid]);
for(int q:states)for(int b=0;b<2;++b){int act=acts[q][b];if((act&3)==(b+2))incoming[act>>2]|=(1<<b);}
ProvMap providers[2];providers[0].reserve(256);providers[1].reserve(256);
for(int h:states){int a=acts[h][0],b=acts[h][1];if((a&3)!=2||(b&3)!=3)continue;int u=a>>2,v=b>>2;for(int bit=0;bit<2;++bit)if(acts[u][bit]>=0&&acts[v][bit]>=0)providers[bit][keyof(acts[u][bit],acts[v][bit])].push_back({h,u,v});}
vector<int>ls,rs;for(int id:dyn){int q=stateid[id];if(incoming[q]==1)ls.push_back(q);if(incoming[q]==2)rs.push_back(q);}
vector<vector<int>> adj(ls.size());
for(int i=0;i<int(ls.size());++i)for(int j=0;j<int(rs.size());++j){int a=ls[i],b=rs[j];Opp opp;opp.a=a;opp.b=b;bool valid=true;for(int bit=0;bit<2;++bit){if(acts[a][bit]==acts[b][bit]){opp.opts[bit].push_back(acts[a][bit]);continue;}auto p=providers[bit].find(keyof(acts[a][bit],acts[b][bit]));if(p!=providers[bit].end())for(auto v:p->second){if(v.h==a||v.h==b||v.u==a||v.u==b||v.v==a||v.v==b)continue;opp.opts[bit].push_back(ai(bit,0,v.h));}if(opp.opts[bit].empty()){valid=false;break;}}if(valid){adj[i].push_back(j);edgepairs.push_back({a,b});candidates.push_back(opp);}}
vector<int>matched(rs.size(),-1),seen(rs.size());
auto augment=[&](auto&&self,int i,int mark)->bool{for(int j:adj[i]){if(seen[j]==mark)continue;seen[j]=mark;if(matched[j]<0||self(self,matched[j],mark)){matched[j]=i;return true;}}return false;};
int f=0;for(int i=0;i<int(ls.size());++i)f+=augment(augment,i,i+1);
if(n-f<=62&&pen==0)f=actualfolds(f);return{n-f,n,f,pen};
}
double value(Stat s){return s.eff+0.008*s.n+s.pen;}
void printmeta(ostream&f,const Meta&m,Stat s,int cycle,int iter){f<<"{\"effective_lower\":"<<s.eff<<",\"nodes\":"<<s.n<<",\"fold_matching\":"<<s.fold<<",\"penalty\":"<<s.pen<<",\"cycle\":"<<cycle<<",\"iteration\":"<<iter<<",\"gate\":"<<m.gate;auto arr=[&](const char*name,auto a){f<<",\""<<name<<"\":[";for(int i=0;i<6;++i)f<<(i?",":"")<<a[i];f<<"]";};arr("order",m.order);arr("parameters",m.perm);arr("antecedent_flip",m.flip);f<<"}"<<endl;}

vector<pair<int,int>> rotated(int target,int direction){
 auto old=shape;vector<pair<int,int>> out;
 auto make=[&](int a,int b){int id=nw+out.size();out.push_back({a,b});return id;};
 auto rec=[&](auto&&self,int ref)->int{
  if(ref<nw)return ref;
  int a=old[ref-nw].first,b=old[ref-nw].second;
  if(target>=1000 ? ref==target-1000 : ids[ref]==target){
   if(direction==0){auto [aa,ab]=old[a-nw];return make(self(self,aa),make(self(self,ab),self(self,b)));}
   auto [ba,bb]=old[b-nw];return make(make(self(self,a),self(self,ba)),self(self,bb));
  }
  return make(self(self,a),self(self,b));
 };
 rec(rec,nw+np-1);if(int(out.size())!=np){cerr<<"rotation size error";exit(2);}return out;
}
void savecandidate(const char*name,const Meta&m,Stat s,int cycle,int it,const vector<pair<int,int>>&sh){
 ofstream f(name);printmeta(f,m,s,cycle,it);
 ofstream a(string(name)+".shape");for(auto [x,y]:sh)a<<x<<" "<<y<<"\n";
 auto w=word(m);ofstream b(string(name)+".word");for(int v:w)b<<v<<" ";b<<"\n";
}
int main(int argc,char**argv){init(argv[1]);int cycles=argc>2?stoi(argv[2]):10000;int seed=argc>3?stoi(argv[3]):799137;rng.seed(seed);Meta initial,bestm;auto initialshape=shape;auto initval=score(initial);cerr<<"INITIAL ";printmeta(cerr,initial,initval,0,0);double best=value(initval);vector<pair<Meta,vector<pair<int,int>>>>pool{{initial,shape}};auto begin=chrono::steady_clock::now();uint64_t count=0;
for(int cycle=0;cycle<cycles;++cycle){auto chosen=pool[rng()%pool.size()];Meta cur=chosen.first;auto curshape=chosen.second;shape=curshape;auto s=score(cur);double cv=value(s);for(int it=0;it<3000;++it){++count;Meta next=cur;auto nextshape=curshape;int type=rng()%100;
if(type<1){int j=rng()%6;next.perm[j]=rng()%6;}else if(type<2){int a=rng()%6,b=rng()%6;swap(next.order[a],next.order[b]);}else if(type==2){int a=rng()%3;int j=a==0?2:a==1?3:5;next.flip[j]^=1;}else if(type==3)next.gate^=1;
else{shape=curshape;score(cur);int target;vector<int>dirs;if(rng()%2){target=nt+rng()%(ncanon-nt);if(leftid[target]>=nt)dirs.push_back(0);if(rightid[target]>=nt)dirs.push_back(1);}else{int ref=nw+rng()%np;auto [a,b]=shape[ref-nw];target=1000+ref;if(a>=nw)dirs.push_back(0);if(b>=nw)dirs.push_back(1);}if(dirs.empty())continue;nextshape=rotated(target,dirs[rng()%dirs.size()]);}
shape=nextshape;auto ns=score(next);double nv=value(ns);double temp=(cycle%3==0?1.0:0.4)*(1.-it/3000.)+0.06;double r=double(rng()>>11)/9007199254740992.;if(nv<=cv||r<exp((cv-nv)/temp)){cur=next;curshape=nextshape;s=ns;cv=nv;if(cv<best){best=cv;bestm=cur;printmeta(cout,cur,s,cycle,it);savecandidate("h2transfer_best.json",cur,s,cycle,it,curshape);if(pool.size()<100)pool.push_back({cur,curshape});}if(s.eff<=62&&s.pen==0&&it%100==0){if(pool.size()<400)pool.push_back({cur,curshape});else if(rng()%5==0)pool[rng()%pool.size()]={cur,curshape};}if(s.eff<=60&&s.pen==0){savecandidate("h2transfer_candidate.json",cur,s,cycle,it,curshape);return 0;}}
}if(cycle%20==0){auto secs=chrono::duration<double>(chrono::steady_clock::now()-begin).count();cerr<<"PROGRESS cycles="<<cycle<<" tries="<<count<<" best="<<best<<" pool="<<pool.size()<<" secs="<<secs<<endl;}}
}
