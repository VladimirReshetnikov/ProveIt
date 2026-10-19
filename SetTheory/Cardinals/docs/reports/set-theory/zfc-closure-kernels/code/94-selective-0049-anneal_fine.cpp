// Fine-atom extension of the attributed routed245 annealer.
// See fine-atom-identities.json; exact AST identities, no commutations.
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
bool permitted(int a,int b){return (!terminal(a)||(allowed[a]&1))&&(!terminal(b)||(allowed[b]&2));}
void collect(Grammar&g,const vector<int>&route){unordered_set<int>seen;vector<int> todo=roots;todo.insert(todo.end(),route.begin(),route.end());while(!todo.empty()){int q=todo.back();todo.pop_back();if(terminal(q)||!seen.insert(q).second)continue;auto it=g.find(q);if(it==g.end()){cerr<<"missing "<<q<<" "<<words[q]<<endl;exit(2);}todo.push_back(it->second.a);todo.push_back(it->second.b);}for(auto it=g.begin();it!=g.end();)if(!seen.count(it->first))it=g.erase(it);else++it;}
bool matches(const Grammar&g,int q,const vector<Constraint>&cs){for(auto c:cs){int v=q;for(char b:c.prefix){auto it=g.find(v);if(it==g.end())return false;v=b=='0'?it->second.a:it->second.b;}if(v!=c.target)return false;}return true;}
bool route_contexts(const Grammar&g,vector<int>&route,mt19937_64&rng,bool randomize=false){for(auto [q,c]:fixed_projections)if(!matches(g,q,vector<Constraint>{c}))return false;for(int i=0;i<(int)groups.size();i++){if(!randomize&&matches(g,route[i],groups[i].cs))continue;vector<int> opts;for(auto [q,r]:g)if(matches(g,q,groups[i].cs))opts.push_back(q);if(opts.empty())return false;route[i]=opts[rng()%opts.size()];}return true;}
Prop wordprop(int,const Grammar&,unordered_map<int,Prop>&,unordered_map<int,Prop>&,unordered_set<int>&);
Prop exprprop(int x,const Grammar&g,unordered_map<int,Prop>&wm,unordered_map<int,Prop>&em,unordered_set<int>&seen){auto it=em.find(x);if(it!=em.end())return it->second;auto e=exprs[x];Prop p;if(e.kind=='L')p={0,0,0};else if(e.kind=='W')p=wordprop(e.a,g,wm,em,seen);else p=join(exprprop(e.a,g,wm,em,seen),exprprop(e.b,g,wm,em,seen));em[x]=p;return p;}
Prop wordprop(int q,const Grammar&g,unordered_map<int,Prop>&wm,unordered_map<int,Prop>&em,unordered_set<int>&seen){auto it=wm.find(q);if(it!=wm.end())return it->second;if(!seen.insert(q).second)return {10000,10000,10000};Prop p;if(terminal(q))p=exprprop(atomExpr.at(q),g,wm,em,seen);else{auto it=g.find(q);Rule r=it==g.end()?oldGrammar.at(q):it->second;p=join(wordprop(r.a,g,wm,em,seen),wordprop(r.b,g,wm,em,seen));}seen.erase(q);wm[q]=p;return p;}
Prop fullprop(const Grammar&g){unordered_map<int,Prop>wm,em;unordered_set<int>seen;return exprprop(originalExpr,g,wm,em,seen);}
void save(const string&path,const Grammar&g,const vector<int>&route,long long iterations,int seed,double elapsed){ofstream f(path);Prop p=fullprop(g);f<<"{\n\"status\":\"FINE_ATOM_ROUTING_GRAMMAR_ONLY\",\n\"rules_count\":"<<g.size()<<",\n\"framework_states\":118,\n\"erase177\":true,\n\"retarget\":-2,\n\"seed\":"<<seed<<",\n\"iterations\":"<<iterations<<",\n\"seconds\":"<<elapsed<<",\n\"properties\":["<<p.lead<<","<<p.zero<<","<<p.depth<<"],\n\"roots\":[";for(size_t i=0;i<roots.size();i++){if(i)f<<",";f<<"\""<<words[roots[i]]<<"\"";}f<<"],\n\"routes\":[";for(size_t i=0;i<route.size();i++){if(i)f<<",";f<<"{\"source\":"<<groups[i].source<<",\"read\":"<<groups[i].read<<",\"word\":\""<<words[route[i]]<<"\"}";}f<<"],\n\"rules\":[\n";vector<int>order;for(auto[q,r]:g)order.push_back(q);sort(order.begin(),order.end(),[](int a,int b){return words[a]<words[b];});for(size_t i=0;i<order.size();i++){auto q=order[i];auto r=g.at(q);if(i)f<<",\n";f<<"[\""<<words[q]<<"\",\""<<words[r.a]<<"\",\""<<words[r.b]<<"\"]";}f<<"\n]}\n";}
int synth_child(Grammar&g,const vector<Constraint>&cs,const vector<int>&active,mt19937_64&rng){
 for(auto c:cs)if(c.prefix.empty()){if(matches(g,c.target,cs))return c.target;return -1;}
 vector<int>opts;for(int q:active)if(matches(g,q,cs))opts.push_back(q);
 if(!opts.empty()&&rng()%5)return opts[rng()%opts.size()];
 int forced[2]={-1,-1};for(auto c:cs){if(c.prefix.size()!=1)return -1;int b=c.prefix[0]-'0';if(forced[b]>=0&&forced[b]!=c.target)return -1;forced[b]=c.target;}
 for(int tries=0;tries<30;tries++){int ab[2]={forced[0],forced[1]};for(int b=0;b<2;b++)if(ab[b]<0){ab[b]=active[rng()%active.size()];if(words[ab[b]].size()>30)ab[b]=active[rng()%active.size()];}if(words[ab[0]].size()+words[ab[1]].size()>80||!permitted(ab[0],ab[1]))continue;int q=intern(words[ab[0]]+words[ab[1]]);g[q]={ab[0],ab[1]};return q;}return -1;
}
bool router_move(Grammar&g,vector<int>&route,mt19937_64&rng){int i=rng()%groups.size();vector<Constraint> cs[2];for(auto c:groups[i].cs){if(c.prefix.empty())return false;cs[c.prefix[0]-'0'].push_back({c.target,c.prefix.substr(1)});}vector<int>active;for(auto[q,r]:g)active.push_back(q);for(auto[c,m]:allowed)active.push_back(c);int ab[2];for(int b=0;b<2;b++){ab[b]=synth_child(g,cs[b],active,rng);if(ab[b]<0)return false;}if(words[ab[0]].size()+words[ab[1]].size()>160||!permitted(ab[0],ab[1]))return false;int q=intern(words[ab[0]]+words[ab[1]]);g[q]={ab[0],ab[1]};route[i]=q;return true;}
int main(int argc,char**argv){if(argc<6){cerr<<"grammar constraints output seconds seed [stopcount=127]"<<endl;return 2;}ifstream f(argv[1]);string output=argv[3];double seconds=stod(argv[4]);int seed=stoi(argv[5]),stopcount=argc>6?stoi(argv[6]):127;int nr,nroot,na;f>>nr>>nroot>>na;vector<tuple<int,string,int>>raw;Grammar initial;for(int i=0;i<nr;i++){int k,q;string s;f>>k>>s>>q;intern(s);raw.push_back({k,s,q});}for(auto[k,s,q]:raw){int id=intern(s),a=intern(s.substr(0,k)),b=intern(s.substr(k));initial[id]={a,b};}for(int i=0;i<nroot;i++){string s;f>>s;roots.push_back(intern(s));}for(int i=0;i<na;i++){string c;int m;f>>c>>m;allowed[intern(c)]=m;}oldGrammar=initial;
 ifstream cf(argv[2]);int ng;cf>>ng;vector<int>initialroute;for(int i=0;i<ng;i++){Group gr;string rt;int nc;cf>>gr.source>>gr.read>>rt>>nc;initialroute.push_back(intern(rt));for(int j=0;j<nc;j++){string p,t;cf>>p>>t;gr.cs.push_back({intern(t),p});}groups.push_back(gr);}int ne,natom;cf>>ne>>originalExpr>>natom;for(int i=0;i<ne;i++){char k;cf>>k;Expr e{k,-1,-1};if(k=='W'){string w;cf>>w;e.a=intern(w);}else if(k=='N')cf>>e.a>>e.b;exprs.push_back(e);}for(int i=0;i<natom;i++){string c;int a;cf>>c>>a;atomExpr[intern(c)]=a;}
 if(argc>7){ifstream lf(argv[7]);int nl;lf>>nl;for(int i=0;i<nl;i++){string w,b,t;lf>>w>>b>>t;int q=intern(w);fixed_projections.push_back({q,{intern(t),b}});if(find(roots.begin(),roots.end(),q)==roots.end())roots.push_back(q);}}
 if(argc>8){ifstream sf(argv[8]);int ns;sf>>ns;initial.clear();for(int i=0;i<ns;i++){int k;string w;sf>>k>>w;int q=intern(w),l=intern(w.substr(0,k)),r=intern(w.substr(k));initial[q]={l,r};}int nrt;sf>>nrt;if(nrt!=int(initialroute.size()))return 8;for(int i=0;i<nrt;i++){string w;sf>>w;initialroute[i]=intern(w);}}
 mt19937_64 rng(seed);uniform_real_distribution<double>uni(0,1);collect(initial,initialroute);if(!route_contexts(initial,initialroute,rng)){cerr<<"initial routes fail"<<endl;return 4;}auto ip=fullprop(initial);cerr<<"INITIAL "<<initial.size()<<" props "<<ip.lead<<","<<ip.zero<<","<<ip.depth<<endl;
 Grammar current=initial,best=initial;vector<int>curroute=initialroute,bestroute=initialroute;int currentn=current.size(),bestn=currentn;long long iter=0,accepted=0,uphill=0,restarts=0,lastbest=0;auto begin=chrono::steady_clock::now();double elapsed=0;save(output,best,bestroute,0,seed,elapsed);
 while((elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count())<seconds){iter++;Grammar next=current;auto nextroute=curroute;int move_kind=rng()%100;bool changed=true;
 if(move_kind<65){vector<int>active;for(auto[q,r]:current)active.push_back(q);int q=active[rng()%active.size()];Rule r=current.at(q);bool left=rng()%2;int a,b,c,part;if(left){if(terminal(r.a))continue;auto s=current.at(r.a);a=s.a;b=s.b;c=r.b;part=intern(words[b]+words[c]);if(!permitted(a,part))continue;if(!next.count(part)){if(!permitted(b,c))continue;next[part]={b,c};}next[q]={a,part};}else{if(terminal(r.b))continue;auto s=current.at(r.b);a=r.a;b=s.a;c=s.b;part=intern(words[a]+words[b]);if(!permitted(part,c))continue;if(!next.count(part)){if(!permitted(a,b))continue;next[part]={a,b};}next[q]={part,c};}}
 else if(move_kind<80){vector<int>active;for(auto[q,r]:current)active.push_back(q);int q=active[rng()%active.size()];string w=words[q];vector<Rule>opts;for(size_t k=1;k<w.size();k++){auto ai=ids.find(w.substr(0,k)),bi=ids.find(w.substr(k));if(ai==ids.end()||bi==ids.end())continue;int x=ai->second,y=bi->second;if((terminal(x)||current.count(x))&&(terminal(y)||current.count(y))&&permitted(x,y))opts.push_back({x,y});}if(opts.empty())changed=false;else next[q]=opts[rng()%opts.size()];}
 else if(move_kind<88)changed=route_contexts(next,nextroute,rng,true);
 else changed=router_move(next,nextroute,rng);
 if(!changed||!route_contexts(next,nextroute,rng))continue;collect(next,nextroute);int nn=next.size();double phase=double(iter%600000)/600000.0;double temp=(0.09+0.50*(1.0-phase));bool ok=nn<=currentn||(nn<=bestn+5&&uni(rng)<exp((currentn-nn)/temp));if(ok){auto p=fullprop(next);if(p.zero>6||p.depth>64)ok=false;}if(ok){if(nn>currentn)uphill++;current=move(next);curroute=move(nextroute);currentn=nn;accepted++;}
 if(currentn==bestn&&uni(rng)<0.015){best=current;bestroute=curroute;}
 if(currentn<bestn){best=current;bestroute=curroute;bestn=currentn;lastbest=iter;save(output,best,bestroute,iter,seed,elapsed);cout<<"BEST "<<bestn<<" iter "<<iter<<" seconds "<<elapsed<<" pool "<<words.size()<<endl;if(bestn<=stopcount)break;}
 if(iter%40000==0)cout<<"progress "<<iter<<" best "<<bestn<<" current "<<currentn<<" sec "<<elapsed<<" pool "<<words.size()<<endl;
 if(iter%40000==0&&iter-lastbest>40000){bool orig=(restarts%5==0);current=orig?initial:best;curroute=orig?initialroute:bestroute;currentn=current.size();restarts++;}
 }
 save(output,best,bestroute,iter,seed,elapsed);cout<<"DONE "<<iter<<" best "<<bestn<<" accepted "<<accepted<<" uphill "<<uphill<<" restarts "<<restarts<<" sec "<<elapsed<<endl;
}
