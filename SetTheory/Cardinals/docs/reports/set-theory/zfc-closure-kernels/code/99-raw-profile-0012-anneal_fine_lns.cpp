// Exact fine-token extension of the attributed routing-aware zero6 annealer.
// Original implementation: ProveIt incoming zfc245-proof-20261018; see NOTICE.
// New here: variable-length atomic keys and joint macro-boundary mutations.
// Search is heuristic. All resulting dictionaries require independent audit.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
using namespace std;
struct Rule{int a,b;}; using Grammar=unordered_map<int,Rule>;
struct Constraint{int target;string prefix;};
struct Group{int source,read;vector<Constraint> cs;};
vector<Group> groups;
vector<pair<int,Constraint>> fixed_projections;
struct Expr{char kind;int a,b;};vector<Expr> exprs;unordered_map<int,int> atomExpr;int originalExpr=-1;
Grammar oldGrammar;
struct Prop{int lead,zero,depth;};
Prop join(Prop a,Prop b){return {1+a.lead,max({1+a.lead,a.zero,b.zero}),1+max(a.depth,b.depth)};}
vector<string> words;unordered_map<string,int> ids;vector<int> roots;unordered_map<int,int> allowed;
int intern(const string&s){auto it=ids.find(s);if(it!=ids.end())return it->second;int q=words.size();ids[s]=q;words.push_back(s);return q;}
bool terminal(int q){return allowed.count(q);}
bool permitted(int a,int b){return (!terminal(a)||(allowed.at(a)&1))&&(!terminal(b)||(allowed.at(b)&2));}
// A malformed trial dictionary is a rejected proposal, not a fatal run.
long long closure_rejections=0;
bool collect(Grammar&g,const vector<int>&route){
 unordered_set<int>seen;vector<int>todo=roots;
 todo.insert(todo.end(),route.begin(),route.end());
 while(!todo.empty()){
  int q=todo.back();todo.pop_back();
  if(terminal(q)||!seen.insert(q).second)continue;
  auto it=g.find(q);
  if(it==g.end())return false;
  todo.push_back(it->second.a);todo.push_back(it->second.b);
 }
 // Erase only after the complete traversal has established closure.
 for(auto it=g.begin();it!=g.end();)
  if(!seen.count(it->first))it=g.erase(it);else++it;
 // Callers must enter a transparent dictionary state, not an atomic key
 // temporarily given a rule by a synthesis proposal and erased above.
 for(int q:route)if(!g.count(q))return false;
 return true;
}

bool matches(const Grammar&g,int q,const vector<Constraint>&cs){for(auto c:cs){int v=q;for(char b:c.prefix){auto it=g.find(v);if(it==g.end())return false;v=b=='0'?it->second.a:it->second.b;}if(v!=c.target)return false;}return true;}
bool route_contexts(const Grammar&g,vector<int>&route,mt19937_64&rng,bool randomize=false){for(auto [q,c]:fixed_projections)if(!matches(g,q,vector<Constraint>{c}))return false;for(int i=0;i<(int)groups.size();i++){if(!randomize&&matches(g,route[i],groups[i].cs))continue;vector<int> opts;for(auto [q,r]:g)if(matches(g,q,groups[i].cs))opts.push_back(q);if(opts.empty())return false;route[i]=opts[rng()%opts.size()];}return true;}
Prop wordprop(int,const Grammar&,unordered_map<int,Prop>&,unordered_map<int,Prop>&,unordered_set<int>&);
Prop exprprop(int x,const Grammar&g,unordered_map<int,Prop>&wm,unordered_map<int,Prop>&em,unordered_set<int>&seen){auto it=em.find(x);if(it!=em.end())return it->second;auto e=exprs[x];Prop p;if(e.kind=='L')p={0,0,0};else if(e.kind=='W')p=wordprop(e.a,g,wm,em,seen);else p=join(exprprop(e.a,g,wm,em,seen),exprprop(e.b,g,wm,em,seen));em[x]=p;return p;}
Prop wordprop(int q,const Grammar&g,unordered_map<int,Prop>&wm,unordered_map<int,Prop>&em,unordered_set<int>&seen){auto it=wm.find(q);if(it!=wm.end())return it->second;if(!seen.insert(q).second)return {10000,10000,10000};Prop p;if(terminal(q))p=exprprop(atomExpr.at(q),g,wm,em,seen);else{auto it=g.find(q);Rule r=it==g.end()?oldGrammar.at(q):it->second;p=join(wordprop(r.a,g,wm,em,seen),wordprop(r.b,g,wm,em,seen));}seen.erase(q);wm[q]=p;return p;}
Prop fullprop(const Grammar&g){unordered_map<int,Prop>wm,em;unordered_set<int>seen;return exprprop(originalExpr,g,wm,em,seen);}
void save(const string&path,const Grammar&g,const vector<int>&route,long long iterations,int seed,double elapsed){ofstream f(path);Prop p=fullprop(g);f<<"{\n\"status\":\"ABSTRACT_FINE_ROUTING_GRAMMAR_ONLY\",\n\"rules_count\":"<<g.size()<<",\n\"framework_states\":118,\n\"erase177\":true,\n\"retarget\":-2,\n\"seed\":"<<seed<<",\n\"iterations\":"<<iterations<<",\n\"seconds\":"<<elapsed<<",\n\"properties\":["<<p.lead<<","<<p.zero<<","<<p.depth<<"],\n\"roots\":[";for(size_t i=0;i<roots.size();i++){if(i)f<<",";f<<"\""<<words[roots[i]]<<"\"";}f<<"],\n\"routes\":[";for(size_t i=0;i<route.size();i++){if(i)f<<",";f<<"{\"source\":"<<groups[i].source<<",\"read\":"<<groups[i].read<<",\"word\":\""<<words[route[i]]<<"\"}";}f<<"],\n\"rules\":[\n";vector<int>order;for(auto[q,r]:g)order.push_back(q);sort(order.begin(),order.end(),[](int a,int b){return words[a]<words[b];});for(size_t i=0;i<order.size();i++){auto q=order[i];auto r=g.at(q);if(i)f<<",\n";f<<"[\""<<words[q]<<"\",\""<<words[r.a]<<"\",\""<<words[r.b]<<"\"]";}f<<"\n]}\n";}
int synth_child(Grammar&g,const vector<Constraint>&cs,const vector<int>&active,mt19937_64&rng){
 for(auto c:cs)if(c.prefix.empty()){if(matches(g,c.target,cs))return c.target;return -1;}
 vector<int>opts;for(int q:active)if(matches(g,q,cs))opts.push_back(q);
 if(!opts.empty()&&rng()%5)return opts[rng()%opts.size()];
 int forced[2]={-1,-1};for(auto c:cs){if(c.prefix.size()!=1)return -1;int b=c.prefix[0]-'0';if(forced[b]>=0&&forced[b]!=c.target)return -1;forced[b]=c.target;}
 for(int tries=0;tries<30;tries++){int ab[2]={forced[0],forced[1]};for(int b=0;b<2;b++)if(ab[b]<0){ab[b]=active[rng()%active.size()];if(words[ab[b]].size()>60)ab[b]=active[rng()%active.size()];}if(words[ab[0]].size()+words[ab[1]].size()>160||!permitted(ab[0],ab[1]))continue;int q=intern(words[ab[0]]+words[ab[1]]);g[q]={ab[0],ab[1]};return q;}return -1;
}
bool router_move(Grammar&g,vector<int>&route,mt19937_64&rng){int i=rng()%groups.size();vector<Constraint> cs[2];for(auto c:groups[i].cs){if(c.prefix.empty())return false;cs[c.prefix[0]-'0'].push_back({c.target,c.prefix.substr(1)});}vector<int>active;for(auto[q,r]:g)active.push_back(q);for(auto[c,m]:allowed)active.push_back(c);int ab[2];for(int b=0;b<2;b++){ab[b]=synth_child(g,cs[b],active,rng);if(ab[b]<0)return false;}if(words[ab[0]].size()+words[ab[1]].size()>320||!permitted(ab[0],ab[1]))return false;int q=intern(words[ab[0]]+words[ab[1]]);g[q]={ab[0],ab[1]};route[i]=q;return true;}

// New: change macro boundaries using exact closed-token substrings. Every
// accepted child has an existing implementation or one newly supplied rule.
bool resegment_move(Grammar&g,vector<int>&route,mt19937_64&rng){
 vector<int> active;for(auto[q,r]:g)if(words[q].size()<=160)active.push_back(q);
 if(active.empty())return false;int q=active[rng()%active.size()];string w=words[q];
 struct Option {Rule top;int newq;Rule child;};vector<Option> opts;
 auto known=[&](const string&v,int side){auto it=ids.find(v);if(it==ids.end())return -1;int a=it->second;
   return ((!terminal(a)&&g.count(a))||(terminal(a)&&(allowed.at(a)&(1<<side))))?a:-1;};
 for(size_t k=1;k<w.size();k++){
   string ls=w.substr(0,k),rs=w.substr(k);int a=known(ls,0),b=known(rs,1);
   if(a>=0&&b>=0)opts.push_back({{a,b},-1,{-1,-1}});
   // Add at most one new pure sequence node, with arbitrary macro boundaries.
   for(int side=0;side<2;side++){
     if((side==0?b:a)<0)continue;string v=side==0?ls:rs;
     int nq=intern(v);if(terminal(nq)||g.count(nq))continue;
     for(size_t j=1;j<v.size();j++){
       int x=known(v.substr(0,j),0),y=known(v.substr(j),1);
       if(x>=0&&y>=0)opts.push_back({side==0?Rule{nq,b}:Rule{a,nq},nq,{x,y}});
     }
   }
 }
 if(opts.empty())return false;auto o=opts[rng()%opts.size()];g[q]=o.top;
 if(o.newq>=0)g[o.newq]=o.child;return true;
}

// Added 2026-10-18: delete a nonmandatory grammar node in one compound move.
// All direct users are resegmented simultaneously; each replacement is an
// exact split of the same semantic word, so the accepted finite audits apply.
bool eliminate_move(Grammar& g,vector<int>& route,mt19937_64& rng){
 vector<int> opts;
 for(auto[q,r]:g){
  if(find(roots.begin(),roots.end(),q)!=roots.end())continue;
  bool forced=false;
  for(auto [root,c]:fixed_projections)if(c.target==q)forced=true;
  for(auto gr:groups)for(auto c:gr.cs)if(c.target==q)forced=true;
  if(!forced)opts.push_back(q);
 }
 if(opts.empty())return false;
 int q=opts[rng()%opts.size()];Rule qr=g.at(q);
 vector<int> parents;
 for(auto[p,r]:g)if(r.a==q||r.b==q)parents.push_back(p);
 shuffle(parents.begin(),parents.end(),rng);
 for(int p:parents){
  Rule pr=g.at(p);string w=words[p];vector<Rule> cuts;
  for(size_t k=1;k<w.size();k++){
   auto ai=ids.find(w.substr(0,k)),bi=ids.find(w.substr(k));
   if(ai==ids.end()||bi==ids.end())continue;
   int x=ai->second,y=bi->second;
   if(x!=q&&y!=q&&(terminal(x)||g.count(x))&&(terminal(y)||g.count(y))&&permitted(x,y))cuts.push_back({x,y});
  }
  if(!cuts.empty()&&(rng()%4!=0)){g[p]=cuts[rng()%cuts.size()];continue;}
  int a,b,c,part;
  if(pr.a==q&&pr.b!=q){
   a=qr.a;b=qr.b;c=pr.b;part=intern(words[b]+words[c]);
   if(part==q||!permitted(a,part)||!permitted(b,c))return false;
   if(!terminal(part)&&!g.count(part))g[part]={b,c};g[p]={a,part};
  }else if(pr.b==q&&pr.a!=q){
   a=pr.a;b=qr.a;c=qr.b;part=intern(words[a]+words[b]);
   if(part==q||!permitted(part,c)||!permitted(a,b))return false;
   if(!terminal(part)&&!g.count(part))g[part]={a,b};g[p]={part,c};
  }else return false;
 }
 g.erase(q);
 // Route selectors are free roots and may switch to a compatible live word.
 return route_contexts(g,route,rng);
}


// New 2026-10-18 joint exact-substring destroy/repair search. The source
// semantics are unchanged by each proposal; bootstrap relaxation is explicit
// in the input locks and still requires an independently checked blank run.
// This optimizer is a heuristic and makes no state-minimality assertion.
int wordmask(int q){return terminal(q)?allowed.at(q):3;}
bool valid_known(int q,const Grammar&g,unordered_map<int,bool>&memo){
 if(terminal(q))return true;
 auto it=memo.find(q);if(it!=memo.end())return it->second;
 auto r=g.find(q);if(r==g.end())return memo[q]=false;
 return memo[q]=valid_known(r->second.a,g,memo)&&valid_known(r->second.b,g,memo);
}
bool repair_word(int target,Grammar&g,mt19937_64&rng){
 string w=words[target];int n=w.size();if(n>1600)return false;
 unordered_map<int,bool> memo;vector<int> vocab;
 for(auto[q,r]:g)if(q!=target&&words[q].size()<w.size()&&valid_known(q,g,memo))vocab.push_back(q);
 for(auto[q,m]:allowed)if(words[q].size()<w.size())vocab.push_back(q);
 shuffle(vocab.begin(),vocab.end(),rng);
 // Every legal binary tree has a left-compatible first leaf and a
 // right-compatible last leaf. Intermediate leaves are resolved by CYK.
 const double inf=1e30;vector<double>dp(n+1,inf);vector<int>prev(n+1,-1),chosen(n+1,-1),num(n+1,999);
 double jitter=double(rng()%5)*0.065;unordered_map<int,double>weights;
 for(int q:vocab)weights[q]=1.0+jitter*(double(rng()%10000)/10000.0);
 dp[0]=0;num[0]=0;
 for(int i=0;i<n;i++)if(dp[i]<inf&&num[i]<30){
  for(int q:vocab){int len=words[q].size(),j=i+len;if(j>n)continue;
   if(i==0&&!(wordmask(q)&1))continue;
   if(j==n&&!(wordmask(q)&2))continue;
   if(w.compare(i,len,words[q])!=0)continue;
   double cost=dp[i]+weights[q];
   if(cost<dp[j]){dp[j]=cost;prev[j]=i;chosen[j]=q;num[j]=num[i]+1;}
  }
 }
 if(chosen[n]<0||num[n]<2||num[n]>30)return false;
 vector<int> toks;for(int j=n;j>0;j=prev[j])toks.push_back(chosen[j]);reverse(toks.begin(),toks.end());
 int m=toks.size();vector<int>pos(1,0);for(int q:toks)pos.push_back(pos.back()+words[q].size());
 struct Cell{double cost=1e30;int key=-1,split=-1;bool known=false;};
 vector<vector<Cell>> tab(m,vector<Cell>(m+1));
 for(int i=0;i<m;i++)tab[i][i+1]={0.0,toks[i],-1,true};
 for(int len=2;len<=m;len++)for(int i=0;i+len<=m;i++){
  int j=i+len;string part=w.substr(pos[i],pos[j]-pos[i]);int key=intern(part);Cell&cell=tab[i][j];cell.key=key;
  if(key!=target&&((terminal(key))||(g.count(key)&&valid_known(key,g,memo)))){cell.cost=0;cell.known=true;continue;}
  if(terminal(key))continue; // Atomic keys are not shadowed by transparent rules.
  for(int k=i+1;k<j;k++){
   auto&a=tab[i][k];auto&b=tab[k][j];
   if(a.cost>=inf||b.cost>=inf||!permitted(a.key,b.key))continue;
   double cost=a.cost+b.cost+1.0+0.000001*double(rng()%10000)/10000.0;
   if(cost<cell.cost){cell.cost=cost;cell.split=k;cell.known=false;}
  }
 }
 if(tab[0][m].cost>=inf)return false;
 auto emit=[&](auto&&self,int i,int j)->void{
  auto c=tab[i][j];if(c.known)return;int k=c.split;self(self,i,k);self(self,k,j);g[c.key]={tab[i][k].key,tab[k][j].key};
 };emit(emit,0,m);return true;
}
bool lns_move(Grammar&g,vector<int>&route,mt19937_64&rng){
 unordered_set<int> forced(roots.begin(),roots.end());
 for(auto [q,c]:fixed_projections){forced.insert(q);forced.insert(c.target);}
 for(auto gr:groups)for(auto c:gr.cs)forced.insert(c.target);
 vector<int>opts;for(auto[q,r]:g)if(!forced.count(q))opts.push_back(q);
 if(opts.empty())return false;
 int nremove=1+((rng()%100<45)?int(rng()%4):0);shuffle(opts.begin(),opts.end(),rng);
 unordered_set<int>dead;int anchor=opts[0];dead.insert(anchor);
 if(nremove>1){
  // Mix adjacent dependency clusters with unrelated dictionary deletions.
  bool local=rng()%2;for(int q:opts)if(int(dead.size())<nremove&&q!=anchor){
   auto r=g.at(q),ar=g.at(anchor);bool close=(r.a==anchor||r.b==anchor||ar.a==q||ar.b==q||r.a==ar.a||r.b==ar.b);
   if(!local||close)dead.insert(q);
  }
 }
 vector<int>parents;for(auto[p,r]:g)if(!dead.count(p)&&(dead.count(r.a)||dead.count(r.b)))parents.push_back(p);
 for(int q:dead)g.erase(q);
 // Short users first can create common repair words for longer users.
 sort(parents.begin(),parents.end(),[&](int a,int b){return words[a].size()<words[b].size();});
 if(rng()%4==0)shuffle(parents.begin(),parents.end(),rng);
 for(int p:parents){g.erase(p);if(!repair_word(p,g,rng))return false;}
 return route_contexts(g,route,rng);
}

int main(int argc,char**argv){if(argc<6){cerr<<"grammar constraints output seconds seed [stopcount=127]"<<endl;return 2;}ifstream f(argv[1]);string output=argv[3];double seconds=stod(argv[4]);int seed=stoi(argv[5]),stopcount=argc>6?stoi(argv[6]):127;long long iteration_limit=argc>9?stoll(argv[9]):0;int nr,nroot,na;f>>nr>>nroot>>na;vector<tuple<int,string,int>>raw;Grammar initial;for(int i=0;i<nr;i++){int k,q;string s;f>>k>>s>>q;intern(s);raw.push_back({k,s,q});}for(auto[k,s,q]:raw){int id=intern(s),a=intern(s.substr(0,k)),b=intern(s.substr(k));initial[id]={a,b};}for(int i=0;i<nroot;i++){string s;f>>s;roots.push_back(intern(s));}for(int i=0;i<na;i++){string c;int m;f>>c>>m;allowed[intern(c)]=m;}oldGrammar=initial;
 ifstream cf(argv[2]);int ng;cf>>ng;vector<int>initialroute;for(int i=0;i<ng;i++){Group gr;string rt;int nc;cf>>gr.source>>gr.read>>rt>>nc;initialroute.push_back(intern(rt));for(int j=0;j<nc;j++){string p,t;cf>>p>>t;gr.cs.push_back({intern(t),p});}groups.push_back(gr);}int ne,natom;cf>>ne>>originalExpr>>natom;for(int i=0;i<ne;i++){char k;cf>>k;Expr e{k,-1,-1};if(k=='W'){string w;cf>>w;e.a=intern(w);}else if(k=='N')cf>>e.a>>e.b;exprs.push_back(e);}for(int i=0;i<natom;i++){string c;int a;cf>>c>>a;atomExpr[intern(c)]=a;}
 if(argc>7){ifstream lf(argv[7]);int nl;lf>>nl;for(int i=0;i<nl;i++){string w,b,t;lf>>w>>b>>t;int q=intern(w);fixed_projections.push_back({q,{intern(t),b}});if(find(roots.begin(),roots.end(),q)==roots.end())roots.push_back(q);}}
 if(argc>8){ifstream sf(argv[8]);int ns;sf>>ns;initial.clear();for(int i=0;i<ns;i++){int k;string w;sf>>k>>w;int q=intern(w),l=intern(w.substr(0,k)),r=intern(w.substr(k));initial[q]={l,r};}int nrt;sf>>nrt;if(nrt!=int(initialroute.size()))return 8;for(int i=0;i<nrt;i++){string w;sf>>w;initialroute[i]=intern(w);}}
 mt19937_64 rng(seed);uniform_real_distribution<double>uni(0,1);if(!collect(initial,initialroute)){cerr<<"initial grammar closure fails"<<endl;return 2;}if(!route_contexts(initial,initialroute,rng)){cerr<<"initial routes fail"<<endl;return 4;}auto ip=fullprop(initial);cerr<<"INITIAL "<<initial.size()<<" props "<<ip.lead<<","<<ip.zero<<","<<ip.depth<<endl;
 Grammar current=initial,best=initial;vector<int>curroute=initialroute,bestroute=initialroute;int currentn=current.size(),bestn=currentn;long long iter=0,accepted=0,uphill=0,restarts=0,lastbest=0;auto begin=chrono::steady_clock::now();double elapsed=0;save(output,best,bestroute,0,seed,elapsed);
 while((elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count())<seconds&&(!iteration_limit||iter<iteration_limit)){iter++;Grammar next=current;auto nextroute=curroute;int move_kind=rng()%100;bool changed=true;
 if(move_kind<48){vector<int>active;for(auto[q,r]:current)active.push_back(q);int q=active[rng()%active.size()];Rule r=current.at(q);bool left=rng()%2;int a,b,c,part;if(left){if(terminal(r.a))continue;auto s=current.at(r.a);a=s.a;b=s.b;c=r.b;part=intern(words[b]+words[c]);if(!permitted(a,part))continue;if(!terminal(part)&&!next.count(part)){if(!permitted(b,c))continue;next[part]={b,c};}next[q]={a,part};}else{if(terminal(r.b))continue;auto s=current.at(r.b);a=r.a;b=s.a;c=s.b;part=intern(words[a]+words[b]);if(!permitted(part,c))continue;if(!terminal(part)&&!next.count(part)){if(!permitted(a,b))continue;next[part]={a,b};}next[q]={part,c};}}
 else if(move_kind<60){vector<int>active;for(auto[q,r]:current)active.push_back(q);int q=active[rng()%active.size()];string w=words[q];vector<Rule>opts;for(size_t k=1;k<w.size();k++){auto ai=ids.find(w.substr(0,k)),bi=ids.find(w.substr(k));if(ai==ids.end()||bi==ids.end())continue;int x=ai->second,y=bi->second;if((terminal(x)||current.count(x))&&(terminal(y)||current.count(y))&&permitted(x,y))opts.push_back({x,y});}if(opts.empty())changed=false;else next[q]=opts[rng()%opts.size()];}
 else if(move_kind<75)changed=resegment_move(next,nextroute,rng);
 else if(move_kind<81)changed=route_contexts(next,nextroute,rng,true);
 else if(move_kind<88)changed=router_move(next,nextroute,rng);
 else if(move_kind<92)changed=eliminate_move(next,nextroute,rng);
 else changed=lns_move(next,nextroute,rng);
 if(!changed||!route_contexts(next,nextroute,rng))continue;if(!collect(next,nextroute)){closure_rejections++;continue;}int nn=next.size();double phase=double(iter%600000)/600000.0;double temp=(0.09+0.50*(1.0-phase));bool ok=nn<=currentn||(nn<=bestn+5&&uni(rng)<exp((currentn-nn)/temp));if(ok){auto p=fullprop(next);if(p.zero>6||p.depth>64)ok=false;}if(ok){if(nn>currentn)uphill++;current=move(next);curroute=move(nextroute);currentn=nn;accepted++;}
 if(currentn==bestn&&uni(rng)<0.04){best=current;bestroute=curroute;}
 if(currentn<bestn){best=current;bestroute=curroute;bestn=currentn;lastbest=iter;save(output,best,bestroute,iter,seed,elapsed);cout<<"BEST "<<bestn<<" iter "<<iter<<" seconds "<<elapsed<<" pool "<<words.size()<<endl;if(bestn<=stopcount)break;}
 if(iter%40000==0)cout<<"progress "<<iter<<" best "<<bestn<<" current "<<currentn<<" sec "<<elapsed<<" pool "<<words.size()<<endl;
 if(iter%40000==0&&iter-lastbest>40000){bool orig=(restarts%5==0);current=orig?initial:best;curroute=orig?initialroute:bestroute;currentn=current.size();restarts++;}
 }
 save(output,best,bestroute,iter,seed,elapsed);cout<<"DONE "<<iter<<" best "<<bestn<<" accepted "<<accepted<<" uphill "<<uphill<<" restarts "<<restarts<<" closure_rejections "<<closure_rejections<<" sec "<<elapsed<<endl;
}
