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
struct Rule { int a,b; };
using Grammar=unordered_map<int,Rule>;
struct Constraint {int root,target;string prefix;};
vector<Constraint> constraints;
struct Expr {char kind;int a,b;};
vector<Expr> exprs;
unordered_map<char,int> atomExpr;
int originalExpr=-1;
Grammar oldGrammar;
struct Prop {int lead,zero,depth;};
Prop join(Prop a,Prop b){return {1+a.lead,max({1+a.lead,a.zero,b.zero}),1+max(a.depth,b.depth)};}

vector<string> words;
unordered_map<string,int> ids;
vector<int> roots;
unordered_map<char,int> allowed;
int intern(const string&s){auto i=ids.find(s);if(i!=ids.end())return i->second;int id=words.size();ids[s]=id;words.push_back(s);return id;}
bool terminal(int q){return words[q].size()==1;}
bool permitted(int a,int b,bool guard){return !guard||((!terminal(a)||(allowed[words[a][0]]&1))&&(!terminal(b)||(allowed[words[b][0]]&2)));}
void collect(Grammar& g){
 unordered_set<int> seen;vector<int> todo=roots;
 while(!todo.empty()){int q=todo.back();todo.pop_back();if(terminal(q)||!seen.insert(q).second)continue;auto it=g.find(q);if(it==g.end()){cerr<<"missing rule "<<q<<endl;exit(2);}todo.push_back(it->second.a);todo.push_back(it->second.b);}
 for(auto it=g.begin();it!=g.end();){if(!seen.count(it->first))it=g.erase(it);else++it;}
}
bool contexts(const Grammar&g){for(auto c:constraints){int q=c.root;for(char b:c.prefix){auto it=g.find(q);if(it==g.end())return false;q=(b=='0'?it->second.a:it->second.b);}if(q!=c.target)return false;}return true;}
Prop wordprop(int,const Grammar&,unordered_map<int,Prop>&,unordered_map<int,Prop>&,unordered_set<int>&);
Prop exprprop(int x,const Grammar&g,unordered_map<int,Prop>&wm,unordered_map<int,Prop>&em,unordered_set<int>&seen){
 auto it=em.find(x);if(it!=em.end())return it->second;auto e=exprs[x];Prop p;
 if(e.kind=='L')p={0,0,0};
 else if(e.kind=='W')p=wordprop(e.a,g,wm,em,seen);
 else p=join(exprprop(e.a,g,wm,em,seen),exprprop(e.b,g,wm,em,seen));
 em[x]=p;return p;
}
Prop wordprop(int q,const Grammar&g,unordered_map<int,Prop>&wm,unordered_map<int,Prop>&em,unordered_set<int>&seen){
 auto it=wm.find(q);if(it!=wm.end())return it->second;
 if(!seen.insert(q).second)return {10000,10000,10000};
 Prop p;
 if(terminal(q))p=exprprop(atomExpr.at(words[q][0]),g,wm,em,seen);
 else {auto it=g.find(q);Rule r=it==g.end()?oldGrammar.at(q):it->second;p=join(wordprop(r.a,g,wm,em,seen),wordprop(r.b,g,wm,em,seen));}
 seen.erase(q);wm[q]=p;return p;
}
Prop fullprop(const Grammar&g){unordered_map<int,Prop>wm,em;unordered_set<int>seen;return exprprop(originalExpr,g,wm,em,seen);}
int depth(int q,const Grammar& g,unordered_map<int,int>&memo){if(terminal(q))return 0;auto i=memo.find(q);if(i!=memo.end())return i->second;auto r=g.at(q);return memo[q]=1+max(depth(r.a,g,memo),depth(r.b,g,memo));}
int maxdepth(const Grammar&g){unordered_map<int,int>m;int d=0;for(int q:roots)d=max(d,depth(q,g,m));return d;}
void save(const string& path,const Grammar&g,long long iterations,int seed,bool guard){
 ofstream f(path);f<<"{\n\"status\":\"ABSTRACT_GRAMMAR_ONLY\",\n\"rules_count\":"<<g.size()<<",\n\"seed\":"<<seed<<",\n\"iterations\":"<<iterations<<",\n\"observed_orientation_guards\":"<<(guard?"true":"false")<<",\n\"maxdepth\":"<<maxdepth(g)<<",\n\"roots\":[";
 for(size_t i=0;i<roots.size();i++){if(i)f<<",";f<<"\""<<words[roots[i]]<<"\"";}f<<"],\n\"rules\":[\n";
 vector<int> order;for(auto [q,r]:g)order.push_back(q);sort(order.begin(),order.end(),[](int a,int b){return words[a]<words[b];});
 for(size_t i=0;i<order.size();i++){int q=order[i];auto r=g.at(q);if(i)f<<",\n";f<<"[\""<<words[q]<<"\",\""<<words[r.a]<<"\",\""<<words[r.b]<<"\"]";}f<<"\n]}\n";
}
int main(int argc,char**argv){
 if(argc<6){cerr<<"input output seconds seed guards[0/1]"<<endl;return 2;}
 ifstream f(argv[1]);string output=argv[2];double seconds=stod(argv[3]);int seed=stoi(argv[4]);bool guard=stoi(argv[5]);int nr,nroot,na;f>>nr>>nroot>>na;
 vector<tuple<int,string,int>> raw;Grammar initial;
 for(int i=0;i<nr;i++){int k,q;string s;f>>k>>s>>q;intern(s);raw.push_back({k,s,q});}
 for(auto [k,s,q]:raw){int id=intern(s),a=intern(s.substr(0,k)),b=intern(s.substr(k));initial[id]={a,b};}
 for(int i=0;i<nroot;i++){string s;f>>s;roots.push_back(intern(s));}
 for(int i=0;i<na;i++){char c;int mask;f>>c>>mask;allowed[c]=mask;}
 oldGrammar=initial;
 if(argc>6){ifstream cf(argv[6]);int nc;cf>>nc;for(int i=0;i<nc;i++){string r,p,t;cf>>r>>p>>t;constraints.push_back({intern(r),intern(t),p});}
 int ne,na;cf>>ne>>originalExpr>>na;for(int i=0;i<ne;i++){char k;cf>>k;Expr e{k,-1,-1};if(k=='W'){string w;cf>>w;e.a=intern(w);}else if(k=='N')cf>>e.a>>e.b;exprs.push_back(e);}for(int i=0;i<na;i++){char c;int a;cf>>c>>a;atomExpr[c]=a;}
 }
 collect(initial);if(!contexts(initial)){cerr<<"initial context error"<<endl;return 4;}if(originalExpr>=0){auto p=fullprop(initial);cerr<<"initial full props "<<p.lead<<","<<p.zero<<","<<p.depth<<endl;if(p.zero>7||p.depth>64)return 5;}
 for(auto [q,r]:initial)if(!permitted(r.a,r.b,guard)){cerr<<"initial guard error"<<endl;return 3;}
 mt19937_64 rng(seed);uniform_real_distribution<double> uni(0,1);
 Grammar current=initial,best=initial;int currentn=current.size(),bestn=currentn;long long iter=0,accepted=0,uphill=0,restarts=0,lastbest=0;
 auto begin=chrono::steady_clock::now();double elapsed=0;
 save(output,best,0,seed,guard);
 while((elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count())<seconds){
  iter++;vector<int> active;active.reserve(current.size());for(auto [q,r]:current)active.push_back(q);int q=active[rng()%active.size()];Rule r=current.at(q);bool left=rng()%2;
  int a,b,c,part;
  if(left){if(terminal(r.a))continue;Rule s=current.at(r.a);a=s.a;b=s.b;c=r.b;part=intern(words[b]+words[c]);}
  else{if(terminal(r.b))continue;Rule s=current.at(r.b);a=r.a;b=s.a;c=s.b;part=intern(words[a]+words[b]);}
  Grammar next=current;
  if(left){if(!permitted(a,part,guard))continue;if(!next.count(part)){if(!permitted(b,c,guard))continue;next[part]={b,c};}next[q]={a,part};}
  else{if(!permitted(part,c,guard))continue;if(!next.count(part)){if(!permitted(a,b,guard))continue;next[part]={a,b};}next[q]={part,c};}
  collect(next);if(!contexts(next))continue;int nn=next.size();
  // Integer-cost annealing. Longer runs repeatedly heat, then cool.
  double phase=double(iter%1200000)/1200000.0;
  double temp=(0.08+0.55*(1.0-phase));
  bool ok=nn<=currentn||(nn<=bestn+5&&uni(rng)<exp((currentn-nn)/temp));
  if(ok&&originalExpr>=0){auto p=fullprop(next);if(p.zero>7||p.depth>64)ok=false;}if(ok){if(nn>currentn)uphill++;current=move(next);currentn=nn;accepted++;}
  if(currentn==bestn&&uni(rng)<0.015)best=current;
  if(currentn<bestn){best=current;bestn=currentn;lastbest=iter;save(output,best,iter,seed,guard);cout<<"BEST "<<bestn<<" iter "<<iter<<" seconds "<<elapsed<<" words "<<words.size()<<endl;if(bestn<=123)break;}
  if(iter%40000==0){cout<<"progress "<<iter<<" best "<<bestn<<" current "<<currentn<<" sec "<<elapsed<<" pool "<<words.size()<<endl;}
  if(iter%20000==0&&iter-lastbest>20000){current=(restarts%5==0?initial:best);currentn=current.size();restarts++;}
 }
 save(output,best,iter,seed,guard);
 cout<<"DONE "<<iter<<" best "<<bestn<<" accepted "<<accepted<<" uphill "<<uphill<<" restarts "<<restarts<<" sec "<<elapsed<<endl;
 return 0;
}
