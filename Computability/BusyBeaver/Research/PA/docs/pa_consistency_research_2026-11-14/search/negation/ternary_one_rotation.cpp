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
#include "ternary_inputs.hpp"
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
    int kind=(m.negmask>>(2*occurrence))&3;
    if(kind==1){v[i]=11;v[i+2]=12;}
    else if(kind==2){v[i]=12;v[i+1]=13;v[i+2]=13;}
    occurrence++;i+=2;
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
 auto aa=attr(g.root);penalty+=3*max(0,aa[2]-6)+3*max(0,aa[3]-5)+max(0,aa[0]-38);
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
 vector<vector<int>> edges(n);
 for(int i=0;i<n;i++)if(!freestate[i]&&incoming[i]==1)for(int j=0;j<n;j++)if(!freestate[j]&&incoming[j]==2){
  int a=OFFSET+i,b=OFFSET+j;bool good=true;
  for(int bit=0;bit<2&&good;bit++){
    if(rows[a][bit]==rows[b][bit])continue;good=false;
    auto it=providers[bit].find(key(rows[a][bit],rows[b][bit]));if(it==providers[bit].end())break;
    for(auto h:it->second){if(all_of(h.begin(),h.end(),[&](int q){return q!=a&&q!=b;})){good=true;break;}}
  }if(good)edges[i].push_back(j);
 }
 vector<int> match(n,-1);int nf=0;
 function<bool(int,vector<char>&)> aug=[&](int a,vector<char>&seen){for(int b:edges[a]){if(seen[b])continue;seen[b]=1;if(match[b]<0||aug(match[b],seen)){match[b]=a;return true;}}return false;};
 for(int i=0;i<n;i++){vector<char> seen(n,0);nf+=aug(i,seen);}
 return {double(actual-nf),actual,nf,aa[0],aa[2]};
}
void output(ostream&o,const G&g,const Meta&m,const Score&s,long long it,const string&label){
 o<<"{\"label\":\""<<label<<"\",\"iteration\":"<<it<<",\"cost\":"<<s.cost<<",\"nodes\":"<<s.nodes<<",\"folds\":"<<s.folds<<",\"height\":"<<s.height<<",\"zero_run\":"<<s.zero<<",\"flip\":"<<m.flip<<",\"gate\":"<<m.g<<",\"negmask\":"<<m.negmask<<",\"roles\":[";
 for(int i=0;i<7;i++)o<<(i?",":"")<<m.var[i];o<<"],\"order\":[";for(int i=0;i<7;i++)o<<(i?",":"")<<m.order[i];
 o<<"],\"root\":"<<g.root<<",\"rules\":[";for(int i=0;i<(int)g.r.size();i++)o<<(i?",":"")<<"["<<g.r[i].first<<","<<g.r[i].second<<"]";o<<"]}\n";o.flush();
}

int main(int argc,char**argv){
 rng.seed(567894);G init{initial_rules,initial_root};Meta baseline;Score best=score(init);long long evals=0,masks=0;ofstream witnesses(argv[1]);
 for(int index=0;index<6561;index++){
  Meta m;int k=index;for(int j=0;j<8;j++){m.negmask|=(k%3)<<(2*j);k/=3;}
  G g=assign(init,word(m));Score v=score(g);evals++;masks++;
  auto accept=[&](const G&t,const Score&z){
   if(z.cost<best.cost){best=z;output(witnesses,t,m,z,evals,"improvement");}
   if(z.cost<62&&z.height<=38&&z.zero<=6){output(witnesses,t,m,z,evals,"winner");return true;}return false;
  };
  if(accept(g,v))return 0;
  for(int i=0;i<(int)g.r.size();i++)for(bool right:{false,true}){
   if((right?g.r[i].first:g.r[i].second)<0)continue;
   G t=reassoc(g,i,right);Score z=score(t);evals++;
   if(accept(t,z))return 0;
  }
  if(index%500==0)cerr<<"masks "<<masks<<" evals "<<evals<<" best "<<best.cost<<"\n";
 }
 cout<<"{\"masks\":"<<masks<<",\"evaluations\":"<<evals<<",\"best_score\":"<<best.cost<<",\"scope\":\"All 3^8 negation encoding masks, original head order and roles, and at most one global rotation of their assigned baseline grammar. Optimistic reader/helper score only.\"}\n";
}
