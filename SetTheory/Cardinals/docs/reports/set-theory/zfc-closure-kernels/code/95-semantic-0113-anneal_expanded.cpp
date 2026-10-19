// Exact fine-word grammar search.  Input provenance and fixed dictionary are in input.json.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
struct Rule{int a,b;};struct Prop{int lead,zero,depth;};using Grammar=unordered_map<int,Rule>;
vector<string> words;unordered_map<string,int> ids;unordered_map<int,int> masks;unordered_map<int,Prop> baseprop;int root,leadbound,depthbound;Grammar decompositions;
int intern(const string&s){auto it=ids.find(s);if(it!=ids.end())return it->second;int q=words.size();words.push_back(s);ids[s]=q;return q;}
bool freeword(int q,int bit){auto it=masks.find(q);return it!=masks.end()&&(it->second&(1<<bit));}
bool available(int q,int bit,const Grammar&g){return freeword(q,bit)||g.count(q);}
bool collect(Grammar&g){unordered_set<int>seen;vector<int>todo={root};while(!todo.empty()){int q=todo.back();todo.pop_back();if(!seen.insert(q).second)continue;auto it=g.find(q);if(it==g.end())return false;auto r=it->second;for(int b:{0,1}){int c=b?r.b:r.a;if(!freeword(c,b))todo.push_back(c);}}for(auto it=g.begin();it!=g.end();)if(!seen.count(it->first))it=g.erase(it);else++it;return true;}
Prop join(Prop a,Prop b){return{a.lead+1,max({a.lead+1,a.zero,b.zero}),max(a.depth,b.depth)+1};}
Prop prop(int q,const Grammar&g,unordered_map<int,Prop>&memo){auto it=memo.find(q);if(it!=memo.end())return it->second;auto r=g.at(q);Prop a=freeword(r.a,0)?baseprop.at(r.a):prop(r.a,g,memo);Prop b=freeword(r.b,1)?baseprop.at(r.b):prop(r.b,g,memo);return memo[q]=join(a,b);}
Prop prop(const Grammar&g){unordered_map<int,Prop>m;return prop(root,g,m);}
vector<Rule> splits(int q,const Grammar&g){vector<Rule>o;const string w=words[q];for(int k=1;k<int(w.size());k++){auto a=ids.find(w.substr(0,k)),b=ids.find(w.substr(k));if(a!=ids.end()&&b!=ids.end()&&available(a->second,0,g)&&available(b->second,1,g))o.push_back({a->second,b->second});}return o;}
bool ensure(Grammar&g,int q,int a,int b,int bit){if(freeword(q,bit)||g.count(q))return true;if(!available(a,0,g)||!available(b,1,g))return false;g[q]={a,b};return true;}
bool materialize(Grammar&g,int q,int bit,int&budget){
 if(available(q,bit,g))return true;
 if(budget<=0||!decompositions.count(q))return false;
 auto r=decompositions.at(q);budget--;
 if(!materialize(g,r.a,0,budget)||!materialize(g,r.b,1,budget))return false;
 g[q]=r;return true;
}
bool mutate(Grammar&g,mt19937_64&rng){vector<int>active;for(auto[q,r]:g)active.push_back(q);int q=active[rng()%active.size()];auto r=g.at(q);int kind=rng()%100;
 if(kind<25){auto opts=splits(q,g);if(opts.empty())return false;g[q]=opts[rng()%opts.size()];return true;}
 bool left=rng()%2;int child=left?r.a:r.b;vector<Rule>opts;
 if(g.count(child)&&rng()%2)opts.push_back(g.at(child));else opts=splits(child,g);
 if(decompositions.count(child)&&(opts.empty()||rng()%3==0)){
  auto r=decompositions.at(child);int budget=3;
  if(materialize(g,r.a,0,budget)&&materialize(g,r.b,1,budget))opts.push_back(r);
 }
 if(opts.empty())return false;auto inner=opts[rng()%opts.size()];
 if(left){int a=inner.a,b=inner.b,c=r.b;int bc=intern(words[b]+words[c]);if(!available(a,0,g)||!ensure(g,bc,b,c,1))return false;g[q]={a,bc};}
 else{int a=r.a,b=inner.a,c=inner.b;int ab=intern(words[a]+words[b]);if(!ensure(g,ab,a,b,0)||!available(c,1,g))return false;g[q]={ab,c};}
 return true;
}
string quoted(const string&s){string t="\"";for(char c:s){if(c=='\\'||c=='\"')t+='\\';t+=c;}return t+'\"';}
void save(const string&path,const Grammar&g,long long iterations,long long seed,double seconds){ofstream f(path);auto p=prop(g);f<<"{\"status\":\"UNVERIFIED_FINE_WORD_GRAMMAR\",\"fixed_rules\":51,\"private_rules\":"<<g.size()<<",\"properties\":["<<p.lead<<","<<p.zero<<","<<p.depth<<"],\"iterations\":"<<iterations<<",\"seed\":"<<seed<<",\"seconds\":"<<seconds<<",\"rules\":[";vector<int>qs;for(auto[q,r]:g)qs.push_back(q);sort(qs.begin(),qs.end());for(size_t i=0;i<qs.size();i++){int q=qs[i];auto r=g.at(q);if(i)f<<",";f<<"["<<quoted(words[q])<<","<<quoted(words[r.a])<<","<<quoted(words[r.b])<<"]";}f<<"]}\n";}
int main(int argc,char**argv){if(argc<5)return 2;ifstream f(argv[1]);string out=argv[2];double seconds=stod(argv[3]);long long seed=stoll(argv[4]);int nf,nr;f>>nf>>nr>>leadbound>>depthbound;
 for(int i=0;i<nf;i++){string w;int m;Prop p;f>>w>>m>>p.lead>>p.zero>>p.depth;int q=intern(w);masks[q]=m;baseprop[q]=p;}
 Grammar initial;for(int i=0;i<nr;i++){string w,a,b;f>>w>>a>>b;initial[intern(w)]={intern(a),intern(b)};}string rt;f>>rt;root=intern(rt);int nd;f>>nd;for(int i=0;i<nd;i++){string w,a,b;f>>w>>a>>b;decompositions[intern(w)]={intern(a),intern(b)};}if(!collect(initial))return 3;auto ip=prop(initial);cerr<<"INITIAL "<<initial.size()<<" "<<ip.lead<<","<<ip.zero<<","<<ip.depth<<" bounds "<<leadbound<<","<<depthbound<<"\n";
 mt19937_64 rng(seed);uniform_real_distribution<double>uni(0,1);Grammar cur=initial,best=initial;int ncur=cur.size(),nbest=ncur;long long iter=0,accepted=0,restarts=0,lastbest=0;auto began=chrono::steady_clock::now();double elapsed=0;save(out,best,0,seed,0);
 while((elapsed=chrono::duration<double>(chrono::steady_clock::now()-began).count())<seconds){iter++;Grammar next=cur;bool changed=false;int count=1+(rng()%5==0?rng()%3:0);for(int k=0;k<count;k++)changed=mutate(next,rng)||changed;if(!changed||!collect(next))continue;int nn=next.size();double phase=double(iter%200000)/200000;double temp=.06+.5*(1-phase);bool ok=nn<=ncur||(nn<=nbest+6&&uni(rng)<exp((ncur-nn)/temp));if(ok){auto p=prop(next);ok=p.zero<=6&&p.lead<=leadbound&&p.depth<=depthbound;}if(ok){cur=move(next);ncur=nn;accepted++;}
 if(ncur==nbest&&uni(rng)<.05){best=cur;}
 if(ncur<nbest){best=cur;nbest=ncur;lastbest=iter;save(out,best,iter,seed,elapsed);cout<<"BEST "<<nbest<<" iter "<<iter<<" sec "<<elapsed<<"\n"<<flush;if(nbest<=76)break;}
 if(iter%20000==0){cout<<"progress "<<iter<<" current "<<ncur<<" best "<<nbest<<" sec "<<elapsed<<" pool "<<words.size()<<"\n"<<flush;if(iter-lastbest>20000){cur=(restarts%5==0)?initial:best;ncur=cur.size();restarts++;}}
 }
 save(out,best,iter,seed,elapsed);cout<<"DONE "<<iter<<" accepted "<<accepted<<" restarts "<<restarts<<" best "<<nbest<<" seconds "<<elapsed<<"\n";
}
