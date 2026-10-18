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
 collect(initial);for(auto [q,r]:initial)if(!permitted(r.a,r.b,guard)){cerr<<"initial guard error"<<endl;return 3;}
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
  collect(next);int nn=next.size();
  // Integer-cost annealing. Longer runs repeatedly heat, then cool.
  double phase=fmod(elapsed,12.0)/12.0;
  double temp=(0.10+0.46*(1.0-phase));
  bool ok=nn<=currentn||(nn<=bestn+3&&uni(rng)<exp((currentn-nn)/temp));
  if(ok){if(nn>currentn)uphill++;current=move(next);currentn=nn;accepted++;}
  if(currentn<bestn){best=current;bestn=currentn;lastbest=iter;save(output,best,iter,seed,guard);cout<<"BEST "<<bestn<<" iter "<<iter<<" seconds "<<elapsed<<" words "<<words.size()<<endl;if(bestn<=123)break;}
  if(iter%40000==0){cout<<"progress "<<iter<<" best "<<bestn<<" current "<<currentn<<" sec "<<elapsed<<" pool "<<words.size()<<endl;}
  if(iter%20000==0&&iter-lastbest>20000){current=(restarts%5==0?initial:best);currentn=current.size();restarts++;}
 }
 save(output,best,iter,seed,guard);
 cout<<"DONE "<<iter<<" best "<<bestn<<" accepted "<<accepted<<" uphill "<<uphill<<" restarts "<<restarts<<" sec "<<elapsed<<endl;
 return 0;
}
