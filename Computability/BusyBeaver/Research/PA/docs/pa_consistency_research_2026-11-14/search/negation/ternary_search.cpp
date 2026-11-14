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
 long long limit=argc>1?stoll(argv[1]):1000000;unsigned long long seed=argc>2?stoull(argv[2]):20261114;
 string prefixout=argc>3?argv[3]:"run";rng.seed(seed);ofstream out(prefixout+".ndjson");
 G init{initial_rules,initial_root};Meta m;G cur=init;Score c=score(cur),best=c;
 output(cout,cur,m,c,0,"baseline");if(c.cost!=62)throw runtime_error("baseline score mismatch");
 array<vector<pair<G,Meta>>,8> pools;array<int,8> poolbest;poolbest.fill(999);
 pools[0].push_back({cur,m});poolbest[0]=62;
 long long accepted=0,evaluations=1,early_skips=0;array<int,8> gatebest;gatebest.fill(999);
 for(int index=0;index<6561;index++){
   int k=index,mask=0;for(int j=0;j<8;j++){mask|=(k%3)<<(2*j);k/=3;}
   Meta mm;mm.negmask=mask;G gg=assign(init,word(mm));Score sc=score(gg);evaluations++;
   if(sc.cost<=best.cost){output(out,gg,mm,sc,-2,"mask_seed");if(sc.cost<best.cost)best=sc;}
   if(sc.cost<=62)pools[0].push_back({gg,mm});
   if(sc.cost<62&&sc.height<=38&&sc.zero<=6){ofstream win(prefixout+"_winner.json");output(win,gg,mm,sc,-2,"mask_winner");return 0;}
 }

 for(int gi=0;gi<NG;gi++){
  Meta mm;mm.g=gi;G gg=assign(init,word(mm));Score sc=score(gg);evaluations++;
  gatebest[gi]=min(gatebest[gi],int(sc.cost));if(sc.cost<best.cost){best=sc;output(out,gg,mm,sc,-1,"seed_improvement");}
  if(sc.cost<poolbest[gi]){pools[gi].clear();poolbest[gi]=sc.cost;pools[gi].push_back({gg,mm});}
  for(int k=0;k<250;k++){
   gg=repair(word(mm),k%2?0.99:3.);sc=score(gg);evaluations++;
   gatebest[gi]=min(gatebest[gi],int(sc.cost));if(sc.cost<best.cost){best=sc;output(out,gg,mm,sc,-1,"seed_improvement");}
   if(sc.cost<poolbest[gi]){pools[gi].clear();poolbest[gi]=sc.cost;}
   if(sc.cost==poolbest[gi])pools[gi].push_back({gg,mm});
  }
  cerr<<"seed gate "<<gi<<" best "<<poolbest[gi]<<" pool "<<pools[gi].size()<<"\n";
 }
 auto record=[&](const G&gg,const Meta&mm,const Score&ss,long long it,const string&label){
  int slot=mm.g;
  gatebest[slot]=min(gatebest[slot],int(ss.cost));
  if(ss.cost<best.cost){best=ss;output(cout,gg,mm,ss,it,label);output(out,gg,mm,ss,it,label);}
  else if(ss.cost<62&&ss.height<=38&&ss.zero<=6)output(out,gg,mm,ss,it,label);
 };
 auto started=chrono::steady_clock::now();
 for(long long i=0;i<limit;i++){
   G next;Meta nm=m;
   if(rnd()<0.10){
    int k=rng()%17;
    if(k<7)nm.var[k]=rng()%heads[nm.flip][k].size();
    else if(k<10)swap(nm.order[rng()%7],nm.order[rng()%7]);
    else if(k==10)nm.g=rng()%NG;else if(k==11)nm.flip^=1;else {int j=rng()%8;nm.negmask=(nm.negmask&~(3<<(2*j)))|((rng()%3)<<(2*j));}
    next=assign(cur,word(nm));
   }else{
    int sel=rng()%cur.r.size();auto[l,r]=cur.r[sel];
    if(l<0&&r<0){early_skips++;continue;}
    bool right=(l>=0&&(r<0||rnd()<0.5));next=reassoc(cur,sel,right);
   }
   Score ns=score(next);evaluations++;record(next,nm,ns,i,"proposal");if(ns.cost<62&&ns.height<=38&&ns.zero<=6){ofstream win(prefixout+"_winner.json");output(win,next,nm,ns,i,"winner");return 0;}
   gatebest[nm.g]=min(gatebest[nm.g],int(ns.cost));
   double temp=0.12+1.0*(1.-double(i%10000)/10000.);
   if(ns.cost<=c.cost||rnd()<exp((c.cost-ns.cost)/temp)){cur=move(next);m=nm;c=ns;accepted++;}
   if(c.cost<best.cost){best=c;output(cout,cur,m,c,i,"improvement");output(out,cur,m,c,i,"improvement");}
   if(c.cost<=poolbest[m.g]+1&&c.height<=38&&c.zero<=6){
    if(c.cost<poolbest[m.g]){poolbest[m.g]=c.cost;pools[m.g].clear();}
    auto&pool=pools[m.g];
    if(pool.size()<1500)pool.push_back({cur,m});else if(rng()%20==0)pool[rng()%pool.size()]={cur,m};
    if(c.cost<62){output(out,cur,m,c,i,"sub196_score");if(pool.size()%100==0)output(cout,cur,m,c,i,"sub196_score");}
   }
   if((i+1)%10000==0){
    int gi=((i+1)/10000)%NG;auto &pool=pools[gi];
    auto &p=pool[rng()%pool.size()];cur=p.first;m=p.second;c=score(cur);
    if(rng()%3==0){
     // Cross a word-change barrier explicitly, then optimize its associations.
     m.g=gi;if(rng()%2)m.flip=rng()%2;if(rng()%2){m.negmask=0;for(int j=0;j<8;j++)m.negmask|=(rng()%3)<<(2*j);}
     int changes=1+rng()%4;
     while(changes--){int k=rng()%11;if(k<7)m.var[k]=rng()%heads[m.flip][k].size();else swap(m.order[rng()%7],m.order[rng()%7]);}
     G proposal=assign(cur,word(m));Score ps=score(proposal);evaluations++;record(proposal,m,ps,i,"restart_assignment");
     for(int trial=0;trial<8;trial++){G rr=repair(word(m),trial%2?.99:3.);Score rs=score(rr);evaluations++;record(rr,m,rs,i,"restart_repair");if(rs.cost<ps.cost){proposal=move(rr);ps=rs;}}
     cur=move(proposal);c=ps;
    }
    if((i+1)%100000==0)cerr<<"iteration "<<i+1<<" best "<<best.cost<<" gate "<<gi<<" poolbest "<<poolbest[gi]<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n";
   }
 }
 for(int gi=0;gi<NG;gi++){
   auto&pool=pools[gi];auto it=min_element(pool.begin(),pool.end(),[](const auto&a,const auto&b){return score(a.first).cost<score(b.first).cost;});
   if(it!=pool.end()){ofstream save(prefixout+"_gate"+to_string(gi)+".json");output(save,it->first,it->second,score(it->first),limit,"final_gate_witness");}
 }
 ofstream summary(prefixout+".json");
 summary<<"{\"seed\":"<<seed<<",\"iteration_slots\":"<<limit<<",\"evaluations\":"<<evaluations<<",\"skips\":"<<early_skips<<",\"accepted\":"<<accepted<<",\"best_effective_reader_score\":"<<best.cost<<",\"fixed_state_term\":134,\"gate_best_scores\":[";
 for(int i=0;i<NG;i++)summary<<(i?",":"")<<gatebest[i];summary<<"],\"scope\":\"Stochastic discovery score with syntactic helper matching; no verified physical table or state lower bound.\"}\n";
}
