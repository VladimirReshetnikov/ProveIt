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
#include <unordered_set>
#include <sstream>
#include <set>
using namespace std;
#include "current_inputs.hpp"
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
struct Score{double cost;int nodes,folds,height,zero;};
constexpr int OFFSET=1000,MAXQ=1400;
int encode(int w,int d,int q){return (q<<2)|(d<<1)|w;}
int target(int x){return x>>2;}

struct FoldOp {int a,b;array<vector<int>,2> choices;};
struct FoldCase {int a,b;array<int,2> acts;};
bool local_valid(const array<array<int,2>,MAXQ>&rows,const vector<FoldCase>&fs){
 array<int,MAXQ> alias; iota(alias.begin(),alias.end(),0);
 array<int,MAXQ> replacement;replacement.fill(-1);
 for(int i=0;i<(int)fs.size();i++){alias[fs[i].a]=fs[i].b;replacement[fs[i].b]=i;}
 // There are finitely many configurations on the two allowed cells.
 // Exact cycle detection replaces the discovery scorer's 64-step cutoff.
 static array<uint32_t,MAXQ*8> seen{};static uint32_t stamp=0;
 for(auto f:fs)for(int p=0;p<2;p++)for(int bit=0;bit<2;bit++){
  int orig=p?f.b:f.a;int origact=rows[orig][bit];int wantq=alias[target(origact)],wantpos=(origact&2)?1:-1,wantbit=origact&1;
  int q=f.b,pos=0,left=p,right=bit,steps=0;
  if(++stamp==0){seen.fill(0);stamp=1;}
  for(;;){
   if(steps&&q==wantq&&pos==wantpos&&left==p&&right==wantbit)break;
   if(pos!=-1&&pos!=0)return false;
   if(q<0||q>=MAXQ)return false;
   int index=((q*2+(pos==0))*2+left)*2+right;
   if(seen[index]==stamp)return false;seen[index]=stamp;
   int read=pos==-1?left:right;int rid=replacement[q];int act=rid<0?rows[q][read]:fs[rid].acts[read];if(act<0)return false;
   if(pos==-1)left=act&1;else right=act&1;pos+=(act&2)?1:-1;q=alias[target(act)];steps++;
  }
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
  if(l==-9||r==-5)penalty+=3;
  if(l==-4&&r==-4)freestate[i]=99;
  else if(l>=0&&r>=0&&freestate[l]==99&&freestate[r]==99)freestate[i]=190;
  if(freestate[i])actual--;
 }
 auto aa=attr(g.root);penalty+=3*max(0,aa[2]-6)+3*max(0,aa[3]-5)+max(0,aa[0]-39);
 if(penalty)return {double(actual+penalty),actual,0,aa[0],aa[2]};
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
 nf=compatible_count(rows,ops,nf);
 return {double(actual-nf),actual,nf,aa[0],aa[2]};
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

G canonical(const G&old){
 Builder out;vector<int> memo(old.r.size(),-99999);
 function<int(int)> rec=[&](int i){
  if(i<0)return i;if(memo[i]!=-99999)return memo[i];
  auto[l,r]=old.r[i];int a=rec(l);int b=rec(r);
  return memo[i]=out.node(a,b);
 };
 out.g.root=rec(old.root);return move(out.g);
}
string serial(const G&g){
 string s;auto put=[&](int x){uint32_t n=uint32_t(x);for(int j=0;j<4;j++)s.push_back(char((n>>(8*j))&255));};
 put(g.root);put(g.r.size());for(auto[a,b]:g.r){put(a);put(b);}return s;
}
vector<int> leafword(const G&g){
 vector<int> w;function<void(int)> rec=[&](int i){if(i<0){w.push_back(i);return;}auto[a,b]=g.r[i];rec(a);rec(b);};rec(g.root);return w;
}
struct Gate{int mask=0,depth=0,zero=0,inczero=0,leftbad=0,rightbad=0;};
Gate gatecheck(const G&g){
 vector<array<int,5>> at(g.r.size());Gate z;
 auto attr=[&](int i){return i<0?symbol_fullattrs[-i-1]:at[i];};
 for(int i=0;i<(int)g.r.size();i++){
  auto[l,r]=g.r[i];auto a=attr(l),b=attr(r);
  at[i]={1+max(a[0],b[0]),1+a[1],max({1+a[1],a[2],b[2]}),max({a[3],b[3],a[4]?1+a[1]:0}),a[4]};
  z.leftbad+=(l==-9);z.rightbad+=(r==-5);
 }
 auto aa=attr(g.root);z.depth=aa[0];z.zero=aa[2];z.inczero=aa[3];
 if(z.zero>6)z.mask|=1;if(z.inczero>5)z.mask|=2;
 if(z.leftbad)z.mask|=4;if(z.rightbad)z.mask|=8;if(z.depth>39)z.mask|=16;
 return z;
}
// Enumerates each possible rotation operation. Result duplication is deliberate;
// canonical full strings, rather than probabilistic hashes, deduplicate results.
void neighbors(const G&g,const function<void(G&&,int)>& accept){
 for(int i=0;i<(int)g.r.size();i++){
  auto[l,r]=g.r[i];
  if(l>=0)accept(canonical(reassoc(g,i,true)),0);
  if(r>=0)accept(canonical(reassoc(g,i,false)),0);
 }
 vector<int> path;
 function<void(int)> walk=[&](int i){
  if(i<0)return;auto[l,r]=g.r[i];
  if(l>=0)accept(canonical(one_rotation(g,path,true)),1);
  if(r>=0)accept(canonical(one_rotation(g,path,false)),1);
  path.push_back(0);walk(l);path.back()=1;walk(r);path.pop_back();
 };
 walk(g.root);
}
struct Record{int first=0,second=0,states=-1,nodes=-1,folds=-1;Gate gates;};
void intmap(ostream&o,const map<int,long long>&m){o<<"{";bool first=true;for(auto[k,v]:m){if(!first)o<<",";first=false;o<<"\""<<k<<"\":"<<v;}o<<"}";}
int main(int argc,char**argv){
 string pref=argc>1?argv[1]:"two_rotation";auto started=chrono::steady_clock::now();
 ofstream candidates(pref+".candidates.ndjson"),ties(pref+".ties.ndjson");ofstream keysfile(pref+".keys.bin",ios::binary);Meta meta;
 G initial=canonical(G{initial_rules,initial_root});auto originalword=leafword(initial);
 assert(originalword.size()==191);
 unordered_map<string,int> ids;vector<Record> records;
 vector<pair<int,G>> firsts;long long calls1[2]={0,0},calls2[2]={0,0};int witnesses=0,nties=0;
 auto insert=[&](const G&g){
  string s=serial(g);auto it=ids.find(s);if(it!=ids.end())return it->second;
  assert(leafword(g)==originalword);
  int id=records.size();Record rec;rec.gates=gatecheck(g);
  if(rec.gates.mask==0){
   Score sc=score(g);rec.states=134+int(sc.cost);rec.nodes=sc.nodes;rec.folds=sc.folds;
   assert(sc.cost==int(sc.cost));
   if(rec.states<195){witnesses++;if(witnesses<=100)output(candidates,g,meta,sc,id,"improvement");cerr<<"IMPROVEMENT id "<<id<<" states "<<rec.states<<"\n";}
   else if(rec.states==195&&nties<30){output(ties,g,meta,sc,id,"tie");nties++;}
  }
  uint32_t keylen=s.size();for(int j=0;j<4;j++)keysfile.put(char((keylen>>(8*j))&255));keysfile.write(s.data(),s.size());
  ids.emplace(move(s),id);records.push_back(rec);return id;
 };
 int baseid=insert(initial);assert(baseid==0&&records[0].states==195);
 neighbors(initial,[&](G&&g,int type){calls1[type]++;int id=insert(g);if(!records[id].first)firsts.push_back({id,g});records[id].first|=1<<type;});
 cerr<<"FIRST operations "<<calls1[0]+calls1[1]<<" distinct "<<firsts.size()<<"\n";
 for(int j=0;j<(int)firsts.size();j++){
  auto &[id,g]=firsts[j];int fmask=records[id].first;
  neighbors(g,[&](G&&h,int type){calls2[type]++;int next=insert(h);for(int f=0;f<2;f++)if(fmask&(1<<f))records[next].second|=1<<(2*f+type);});
  if(j%25==24)cerr<<"SECOND parents "<<j+1<<"/"<<firsts.size()<<" distinct_union "<<records.size()<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n";
 }
 ofstream census(pref+".census.tsv");census<<"id\tfirst_types\tsecond_types\tgate_mask\tstates\treaders\tfolds\tax_depth\tmax_zero\tmax_inc_zero\tleft_node142\tright_node72\n";
 long long n1=0,n2=0,nexact2only=0,admiss1=0,admiss2=0,admissNew2=0,admissUnion=0;
 map<int,long long> hist1,hist2,histnew2,histunion,masks1,masks2;long long comps[4]={0,0,0,0};
 for(int id=0;id<(int)records.size();id++){
  auto &r=records[id];auto z=r.gates;
  census<<id<<'\t'<<r.first<<'\t'<<r.second<<'\t'<<z.mask<<'\t'<<r.states<<'\t'<<r.nodes<<'\t'<<r.folds<<'\t'<<z.depth<<'\t'<<z.zero<<'\t'<<z.inczero<<'\t'<<z.leftbad<<'\t'<<z.rightbad<<'\n';
  if(!z.mask){admissUnion++;histunion[r.states]++;}
  if(r.first){n1++;masks1[z.mask]++;if(!z.mask){admiss1++;hist1[r.states]++;}}
  if(r.second){n2++;masks2[z.mask]++;if(!z.mask){admiss2++;hist2[r.states]++;}for(int k=0;k<4;k++)comps[k]+=bool(r.second&(1<<k));}
  if(r.second&&!r.first&&id){nexact2only++;if(!z.mask){admissNew2++;histnew2[r.states]++;}}
 }
 ofstream o(pref+".summary.json");
 o<<"{\n\"scope\":\"All global subtree and single-occurrence binary rotations of the PA195 AX macro tree, at one or two operations; invalid intermediate grammars retained.\",\n";
 o<<"\"canonical_dedup\":\"Full collision-safe canonical ordered-tree DAG serialization; hashes are only container accelerators.\",\n";
 o<<"\"macro_tokens\":"<<originalword.size()<<",\n\"baseline_states\":195,\n\"first_operation_counts\":{\"global\":"<<calls1[0]<<",\"single_occurrence\":"<<calls1[1]<<"},\n";
 o<<"\"second_operation_counts_from_distinct_first_grammars\":{\"global\":"<<calls2[0]<<",\"single_occurrence\":"<<calls2[1]<<"},\n";
 o<<"\"distinct_one_step\":"<<n1<<",\n\"distinct_two_step\":"<<n2<<",\n\"distinct_minimum_distance_two\":"<<nexact2only<<",\n\"distinct_union_including_baseline\":"<<records.size()<<",\n";
 o<<"\"admissible_one_step\":"<<admiss1<<",\n\"admissible_two_step\":"<<admiss2<<",\n\"admissible_minimum_distance_two\":"<<admissNew2<<",\n\"admissible_union_including_baseline\":"<<admissUnion<<",\n";
 o<<"\"composition_distinct_counts\":{\"global_global\":"<<comps[0]<<",\"global_local\":"<<comps[1]<<",\"local_global\":"<<comps[2]<<",\"local_local\":"<<comps[3]<<"},\n";
 o<<"\"state_histogram_one_step\":";intmap(o,hist1);o<<",\n\"state_histogram_two_step\":";intmap(o,hist2);o<<",\n\"state_histogram_minimum_distance_two\":";intmap(o,histnew2);o<<",\n\"state_histogram_union\":";intmap(o,histunion);
 o<<",\n\"gate_masks_one_step\":";intmap(o,masks1);o<<",\n\"gate_masks_two_step\":";intmap(o,masks2);
 o<<",\n\"gate_mask_meaning\":{\"1\":\"maximum zero run exceeds6\",\"2\":\"maximum zero run ending in INC exceeds5\",\"4\":\"node142 occurs as left child\",\"8\":\"node72 occurs as right child\",\"16\":\"AX expanded depth exceeds39\"},\n";
 o<<"\"improving_grammars\":"<<witnesses<<",\n\"witness_records_written\":"<<min(witnesses,100)<<",\n\"exact_compatible_scoring\":true,\n\"local_compatibility_uses_exact_cycle_detection\":true,\n\"full_runtime_checked_by_this_program\":false,\n\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n}\n";
 cerr<<"DONE distinct "<<records.size()<<" admissible "<<admissUnion<<" improving "<<witnesses<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n";
}
