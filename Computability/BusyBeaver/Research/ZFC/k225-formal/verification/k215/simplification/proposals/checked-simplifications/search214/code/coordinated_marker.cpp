// Coordinated 215->214 search: two marker folds, one new helper, temporary tags.
// Exact finite-window joins are synthesis filters, not complete correctness.
// In contrast to the earlier provider search, all new rows are active during
// each trial and retained folded controls may be revisited by provider paths.
#include <iostream>
#include <fstream>
#include <vector>
#include <array>
#include <chrono>
#include <algorithm>
#include <string>
using namespace std;
struct Tr{int w,d,t;}; struct Config{int q,h,tape;};
struct Pair{int p,q,b,side,pm,qm;};
struct Case{int origin,mask;vector<Config> old;};
Tr T[1000][2];vector<int> masks[1000],states;vector<Case> cases[1000][2];
int R,Start,Cap;constexpr int H=999;
vector<Config> trace(int q,int tape){
 int h=0;vector<Config>a;
 for(int k=0;k<Cap;k++){
  int j=h+R;if(j<0||j>2*R||q==254)break;
  auto tr=T[q][(tape>>j)&1];tape=(tape&~(1<<j))|(tr.w<<j);h+=tr.d;q=tr.t;
  a.push_back({q,h,tape});
 }return a;
}
inline int mapq(int q,const Pair&a,const Pair&c){return q==a.q?a.p:q==c.q?c.p:q;}
bool test(const Case& cs,const Pair&a,const Pair&c,int tag0,int v0,int v1){
 int tape=cs.mask,h=0,q=mapq(cs.origin,a,c);
 for(int step=0;step<Cap;step++){
  int j=h+R;if(j<0||j>2*R||q==254)return false;
  int b=(tape>>j)&1;Tr tr;
  if(q==H)tr={b,-a.side,b==0?v0:v1};
  else if(q==a.p&&b==a.b)tr={tag0,a.side,H};
  else if(q==c.p&&b==c.b)tr={1-tag0,c.side,H};
  else tr=T[q][b];
  tape=(tape&~(1<<j))|(tr.w<<j);h+=tr.d;q=mapq(tr.t,a,c);
  for(const auto& g:cs.old)if(q==mapq(g.q,a,c)&&h==g.h&&tape==g.tape)return true;
 }return false;
}
int main(int argc,char**argv){
 if(argc!=4){cerr<<"usage: coordinated_marker INPUT PAIRS CAP\n";return 2;}
 ifstream f(argv[1]);int ns;if(!(f>>R>>Start>>ns)){cerr<<"bad input header\n";return 2;}Cap=stoi(argv[3]);
 if(R<1||R>10||ns<1||ns>998||Cap<1||Cap>4096){cerr<<"input domain\n";return 2;}
 for(int i=0;i<ns;i++){
  int q,n;if(!(f>>q)||q<0||q>=H){cerr<<"bad control\n";return 2;}states.push_back(q);for(int b=0;b<2;b++)f>>T[q][b].w>>T[q][b].d>>T[q][b].t;
  f>>n;for(int j=0;j<n;j++){int m;f>>m;masks[q].push_back(m);}
 }
 vector<Pair> pairs;ifstream pf(argv[2]);Pair e;while(pf>>e.p>>e.q>>e.b>>e.side>>e.pm>>e.qm)pairs.push_back(e);
 for(int q:states)for(int m:masks[q])cases[q][(m>>R)&1].push_back({q,m,trace(q,m)});
 unsigned long long attempts=0,first=0;int families=0,hits=0;auto started=chrono::steady_clock::now();
 for(int ia=0;ia<(int)pairs.size();ia++)for(int ic=ia+1;ic<(int)pairs.size();ic++){
  const Pair&a=pairs[ia],&c=pairs[ic];if(a.side!=c.side)continue;
  vector<int> o={a.p,a.q,c.p,c.q};sort(o.begin(),o.end());if(unique(o.begin(),o.end())!=o.end()||binary_search(o.begin(),o.end(),Start))continue;
  // Equal unmodified rows are guaranteed by pair generator, including after maps.
  vector<const Case*> tests;array<vector<Case>*,4> sets={&cases[a.p][a.b],&cases[a.q][a.b],&cases[c.p][c.b],&cases[c.q][c.b]};
  size_t n=0;for(auto s:sets)n=max(n,s->size());
  for(size_t j=0;j<n;j++)for(auto s:sets)if(j<s->size())tests.push_back(&(*s)[j]);
  for(int tag=0;tag<2;tag++){
   families++;
   for(int v0:states)if(v0!=a.q&&v0!=c.q)for(int v1:states)if(v1!=a.q&&v1!=c.q){
    attempts++;bool ok=true;size_t k=0;
    for(const auto*cs:tests){if(!test(*cs,a,c,tag,v0,v1)){ok=false;break;}k++;}
    if(k>0)first++;
    if(ok){hits++;cout<<"HIT "<<a.p<<" "<<a.q<<" "<<a.b<<" "<<a.side<<" "<<c.p<<" "<<c.q<<" "<<c.b<<" "<<tag<<" "<<v0<<" "<<v1<<" cases "<<tests.size()<<"\n";cout.flush();}
   }
  }
 }
 double secs=chrono::duration<double>(chrono::steady_clock::now()-started).count();
 cout<<"END radius "<<R<<" cap "<<Cap<<" families "<<families<<" attempts "<<attempts<<" first "<<first<<" hits "<<hits<<" seconds "<<secs<<"\n";
}
