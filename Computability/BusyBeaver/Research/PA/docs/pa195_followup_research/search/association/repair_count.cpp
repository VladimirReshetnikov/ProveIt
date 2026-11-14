#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <random>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
using namespace std;
#include "repair_count_inputs.hpp"
// This is a discovery score. Accepted folds require separate physical checking.
using U=uint64_t;
U key(int a,int b){return (U(uint32_t(a))<<32)|uint32_t(b);}
mt19937_64 rng;
double rnd(){return double(rng()>>11)*0x1.0p-53;}
struct Meta{int flip=0,g=0,negmask=0;array<int,7> var={0,0,0,0,0,0,0},order={0,1,2,3,4,5,6};};
vector<int> word(const Meta&m){
  vector<int> v=prefix;
  for(int j:m.order){const auto&w=heads[m.flip][j][m.var[j]];v.insert(v.end(),w.begin(),w.end());}
  const auto&w=gate[m.flip][m.g];v.insert(v.end(),w.begin(),w.end());
  v.insert(v.end(),suffix.begin(),suffix.end());
  int occurrence=0;
  for(int i=0;i+2<(int)v.size();i++)if(v[i]==7&&v[i+1]==3&&v[i+2]==2){
    if(m.negmask&(1<<occurrence)){v[i]=11;v[i+2]=12;}occurrence++;i+=2;
  }
  assert(occurrence==8);return v;
}
struct G{vector<pair<int,int>> r;int root=-1;};
struct Builder{
 G g;unordered_map<U,int> ids;
 int node(int a,int b){U k=key(a,b);auto f=ids.find(k);if(f!=ids.end())return f->second;int id=g.r.size();ids[k]=id;g.r.emplace_back(a,b);return id;}
};
G reassoc(const G&old,int selected,bool right){
 Builder b;vector<int>memo(old.r.size(),-99999);
 function<int(int)> rec=[&](int x){
  if(x<0)return x;if(memo[x]!=-99999)return memo[x];
  auto [l,r]=old.r[x];int out;
  if(x==selected){
    if(right){auto [a,c]=old.r[l];out=b.node(rec(a),b.node(rec(c),rec(r)));}
    else{auto [a,c]=old.r[r];out=b.node(b.node(rec(l),rec(a)),rec(c));}
  }else out=b.node(rec(l),rec(r));
  return memo[x]=out;
 };b.g.root=rec(old.root);return move(b.g);
}
G assign(const G&old,const vector<int>&w){
 Builder b;int pos=0;
 function<int(int)> rec=[&](int x){if(x<0)return -1-w.at(pos++);auto[a,c]=old.r[x];int l=rec(a),r=rec(c);return b.node(l,r);};
 b.g.root=rec(old.root);assert(pos==(int)w.size());return move(b.g);
}
G repair(const vector<int>&w,double noise){
 vector<int> seq;for(int x:w)seq.push_back(-1-x);Builder b;
 while(seq.size()>1){
  map<pair<int,int>,int> counts;
  for(int i=0;i+1<(int)seq.size();i++)counts[{seq[i],seq[i+1]}]++;
  double best=-1;pair<int,int> picked;
  for(auto [p,c]:counts){double s=c+rnd()*noise;if(s>best){best=s;picked=p;}}
  int n=b.node(picked.first,picked.second);vector<int> next;
  for(int i=0;i<(int)seq.size();i++)if(i+1<(int)seq.size()&&make_pair(seq[i],seq[i+1])==picked){next.push_back(n);i++;}else next.push_back(seq[i]);
  seq=move(next);
 }
 b.g.root=seq[0];return move(b.g);
}
struct Score{double cost;int nodes,folds,height,zero,viol;};
constexpr int OFFSET=1000,MAXQ=1400;
int encode(int w,int d,int q){return (q<<2)|(d<<1)|w;}
int target(int x){return x>>2;}

struct FoldOp {int a,b;array<vector<int>,2> choices;};
struct FoldCase {int a,b;array<int,2> acts;};
bool local_valid(const array<array<int,2>,MAXQ>&rows,const vector<FoldCase>&fs){
 array<int,MAXQ> alias; iota(alias.begin(),alias.end(),0);
 array<int,MAXQ> replacement;replacement.fill(-1);
 for(int i=0;i<(int)fs.size();i++){alias[fs[i].a]=fs[i].b;replacement[fs[i].b]=i;}
 for(auto f:fs)for(int p=0;p<2;p++)for(int bit=0;bit<2;bit++){
  int orig=p?f.b:f.a;int origact=rows[orig][bit];int wantq=alias[target(origact)],wantpos=(origact&2)?1:-1,wantbit=origact&1;
  int q=f.b,pos=0,left=p,right=bit;bool done=false;
  for(int k=0;k<64;k++){
   if(k&&q==wantq&&pos==wantpos&&left==p&&right==wantbit){done=true;break;}
   if(pos!=-1&&pos!=0)return false;
   int read=pos==-1?left:right;int rid=replacement[q];int act=rid<0?rows[q][read]:fs[rid].acts[read];if(act<0)return false;
   if(pos==-1)left=act&1;else right=act&1;pos+=(act&2)?1:-1;q=alias[target(act)];
  }
  if(!done)return false;
 }
 return true;
}
int compatible_count(const array<array<int,2>,MAXQ>&rows,const vector<FoldOp>&ops,int bound){
 vector<FoldCase>fs;array<char,MAXQ>used{};
 for(int size=bound;size>0;size--){
  function<bool(int)> search=[&](int i){
   if((int)fs.size()==size)return local_valid(rows,fs);
   if(i==(int)ops.size()||(int)fs.size()+(int)ops.size()-i<size)return false;
   auto &o=ops[i];
   if(!used[o.a]&&!used[o.b]){
    used[o.a]=used[o.b]=1;
    for(int x:o.choices[0])for(int y:o.choices[1]){fs.push_back({o.a,o.b,{x,y}});bool ok=search(i+1);fs.pop_back();if(ok){used[o.a]=used[o.b]=0;return true;}}
    used[o.a]=used[o.b]=0;
   }
   return search(i+1);
  };
  if(search(0))return size;
 }
 return 0;
}

Score score(const G&g){
 int n=g.r.size();vector<array<int,5>>at(n);vector<int>freestate(n,0);int actual=n,penalty=0;
 auto attr=[&](int i){return i<0?symbol_fullattrs[-i-1]:at[i];};
 for(int i=0;i<n;i++){
  auto [l,r]=g.r[i];auto a=attr(l),b=attr(r);
  at[i]={1+max(a[0],b[0]),1+a[1],max({1+a[1],a[2],b[2]}),max({a[3],b[3],a[4]?1+a[1]:0}),a[4]};
  if(l==-9||r==-5)penalty++;
  if(l==-4&&r==-4)freestate[i]=99;
  else if(l>=0&&r>=0&&freestate[l]==99&&freestate[r]==99)freestate[i]=190;
  if(freestate[i])actual--;
 }
 
 vector<array<int,8>> counts(n);vector<int> leafcounts(n);
 auto nc=[&](int x){return x<0?symbol_leaf_counts[-x-1]:leafcounts[x];};
 auto bc=[&](int x,int z){return x<0?bad_leaves[-x-1][z]:counts[x][z];};
 for(int i=0;i<n;i++){auto[l,r]=g.r[i];leafcounts[i]=nc(l)+nc(r);counts[i][7]=leafcounts[i];for(int z=0;z<7;z++)counts[i][z]=bc(l,z+1)+bc(r,0);}
 auto aa=attr(g.root);penalty+=bc(g.root,0)+max(0,aa[0]-39);


 array<array<int,2>,MAXQ> rows;for(auto&x:rows)x={-1,-1};vector<int> states;
 for(auto r:base_rows){rows[r[0]][r[1]]=encode(r[2],r[3],r[4]);if(!r[1])states.push_back(r[0]);}
 auto st=[&](int i){return i<0?symbol_states[-i-1]:(freestate[i]?freestate[i]:OFFSET+i);};
 for(int i=0;i<n;i++){
  if(freestate[i])continue;
  auto [a,b]=g.r[i];
  for(int bit=0;bit<2;bit++){int child=bit?b:a;rows[OFFSET+i][bit]=(child<0&&symbol_states[-child-1]==302)?encode(0,0,302):encode(bit,1,st(child));}
  states.push_back(OFFSET+i);
 }
 rows[101][1]=encode(1,1,st(g.root));
 vector<int> incoming(n,0);
 for(int q:states)for(int bit=0;bit<2;bit++){
  int x=rows[q][bit],t=target(x);if((x&3)==(2+bit)&&t>=OFFSET&&t<OFFSET+n)incoming[t-OFFSET]|=1<<bit;
 }
 array<unordered_map<U,vector<array<int,3>>>,2> providers;
 for(int q:states){
  auto a=rows[q];if((a[0]&3)!=2||(a[1]&3)!=3)continue;
  int u=target(a[0]),v=target(a[1]);
  for(int bit=0;bit<2;bit++)if(u<MAXQ&&v<MAXQ&&rows[u][bit]>=0&&rows[v][bit]>=0)providers[bit][key(rows[u][bit],rows[v][bit])].push_back({q,u,v});
 }

 vector<vector<int>> edges(n);vector<FoldOp> ops;
 for(int i=0;i<n;i++)if(!freestate[i]&&incoming[i]==1)for(int j=0;j<n;j++)if(!freestate[j]&&incoming[j]==2){
  int a=OFFSET+i,b=OFFSET+j;FoldOp op{a,b,{}};
  for(int bit=0;bit<2;bit++){
    if(rows[a][bit]==rows[b][bit]){op.choices[bit].push_back(rows[a][bit]);continue;}
    auto it=providers[bit].find(key(rows[a][bit],rows[b][bit]));if(it==providers[bit].end())continue;
    for(auto h:it->second)if(all_of(h.begin(),h.end(),[&](int q){return q!=a&&q!=b;}))op.choices[bit].push_back(encode(bit,0,h[0]));
  }
  if(!op.choices[0].empty()&&!op.choices[1].empty()){edges[i].push_back(j);ops.push_back(move(op));}
 }
 vector<int> match(n,-1);int nf=0;
 function<bool(int,vector<char>&)> aug=[&](int a,vector<char>&seen){for(int b:edges[a]){if(seen[b])continue;seen[b]=1;if(match[b]<0||aug(match[b],seen)){match[b]=a;return true;}}return false;};
 for(int i=0;i<n;i++){vector<char> seen(n,0);nf+=aug(i,seen);}
 if(actual-nf>64)return {double(actual-nf),actual,nf,aa[0],aa[2],penalty};
 nf=compatible_count(rows,ops,nf);
 return {double(actual-nf),actual,nf,aa[0],aa[2],penalty};
}
void output(ostream&o,const G&g,const Meta&m,const Score&s,long long it,const string&label){
 o<<"{\"label\":\""<<label<<"\",\"iteration\":"<<it<<",\"cost\":"<<s.cost<<",\"nodes\":"<<s.nodes<<",\"folds\":"<<s.folds<<",\"height\":"<<s.height<<",\"zero_run\":"<<s.zero<<",\"flip\":"<<m.flip<<",\"gate\":"<<m.g<<",\"negmask\":"<<m.negmask<<",\"roles\":[";
 for(int i=0;i<7;i++)o<<(i?",":"")<<m.var[i];o<<"],\"order\":[";for(int i=0;i<7;i++)o<<(i?",":"")<<m.order[i];
 o<<"],\"root\":"<<g.root<<",\"rules\":[";for(int i=0;i<(int)g.r.size();i++)o<<(i?",":"")<<"["<<g.r[i].first<<","<<g.r[i].second<<"]";o<<"]}\n";o.flush();
}
G one_rotation(const G&old,vector<int> path,bool right){
 Builder b;vector<int>memo(old.r.size(),-99999);
 function<int(int)> cp=[&](int x){if(x<0)return x;if(memo[x]!=-99999)return memo[x];auto[l,r]=old.r[x];return memo[x]=b.node(cp(l),cp(r));};
 function<int(int,int)> rec=[&](int x,int k){auto[l,r]=old.r[x];if(k==(int)path.size()){
  if(right){auto[a,c]=old.r[l];return b.node(cp(a),b.node(cp(c),cp(r)));}
  else{auto[a,c]=old.r[r];return b.node(b.node(cp(l),cp(a)),cp(c));}
 }return path[k]?b.node(cp(l),rec(r,k+1)):b.node(rec(l,k+1),cp(r));};
 b.g.root=rec(old.root,0);return move(b.g);
}
int main(int argc,char**argv){
 long long limit=argc>1?stoll(argv[1]):3000000;unsigned long long seed=argc>2?stoull(argv[2]):19901;string pref=argc>3?argv[3]:"repair";rng.seed(seed);ofstream out(pref+".ndjson");
 Meta m;G base{initial_rules,initial_root},near{near_rules,near_root},cur=near;Score sc=score(cur);output(cout,cur,m,sc,0,"seed");cerr<<"VIOL "<<sc.viol<<"\n";
 array<vector<pair<G,Score>>,70> pools;array<int,70> bv;bv.fill(999);for(auto g:{base,near}){auto x=score(g);int e=int(x.cost);if(x.viol<bv[e]){bv[e]=x.viol;pools[e].clear();}pools[e].push_back({g,x});}
 double weight=.5;auto started=chrono::steady_clock::now();
 for(long long i=0;i<limit;i++){
  G ng;
  if(rnd()<.6){int sel=rng()%cur.r.size();auto[l,r]=cur.r[sel];if(l<0&&r<0)continue;bool right=l>=0&&(r<0||rnd()<.5);ng=reassoc(cur,sel,right);}
  else{vector<pair<int,vector<int>>>ns;vector<int>p;function<void(int)> visit=[&](int x){if(x<0)return;ns.push_back({x,p});auto[l,r]=cur.r[x];p.push_back(0);visit(l);p.back()=1;visit(r);p.pop_back();};visit(cur.root);auto[sel,path]=ns[rng()%ns.size()];auto[l,r]=cur.r[sel];if(l<0&&r<0)continue;bool right=l>=0&&(r<0||rnd()<.5);ng=one_rotation(cur,path,right);}
  Score ns=score(ng);int e=int(ns.cost);if(e>64||ns.viol>30)continue;
  if(e<61&&ns.viol==0){output(out,ng,m,ns,i,"VALID_CANDIDATE");cerr<<"FOUND "<<i<<"\n";return 0;}
  if(ns.viol<bv[e]){bv[e]=ns.viol;pools[e].clear();output(out,ng,m,ns,i,"pareto");cerr<<"PARETO "<<i<<" e "<<e<<" v "<<ns.viol<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n";}
  if(ns.viol==bv[e]){auto&pool=pools[e];if(pool.size()<200)pool.push_back({ng,ns});else if(rng()%20==0)pool[rng()%pool.size()]={ng,ns};}
  double diff=ns.cost+weight*ns.viol-sc.cost-weight*sc.viol;double temp=.05+.40*(1.-double(i%10000)/10000.);
  if(diff<=0||rnd()<exp(-diff/temp)){cur=move(ng);sc=ns;}
  if(i&&i%10000==0){int key;do{key=59+rng()%6;}while(pools[key].empty());auto&point=pools[key][rng()%pools[key].size()];cur=point.first;sc=point.second;weight=array<double,6>{.1,.2,.4,.7,1.2,2.}[rng()%6];}
  if(i%100000==0&&i)cerr<<"STATUS "<<i<<" current "<<sc.cost<<"/"<<sc.viol<<" best60 "<<bv[60]<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n";
 }
 for(int e=58;e<=64;e++){for(int j=0;j<min(20,(int)pools[e].size());j++)output(out,pools[e][j].first,m,pools[e][j].second,limit,"final");}
 cerr<<"DONE best60 "<<bv[60]<<"\n";
}
