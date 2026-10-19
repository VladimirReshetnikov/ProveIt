// Independently authored grammar search. Reads only mathematical data.
#include <bits/stdc++.h>
using namespace std;
using AB=pair<int,int>;
struct Pr{int lead,run,depth;};
struct Nd{char tag;int a,b;};
vector<string> words; vector<int>mask,atom; unordered_map<string,int>ids;
map<int,AB> baseline,oldrules;vector<int> roots;vector<tuple<int,int,int>> locks;vector<tuple<int,string,int>> cons;vector<Nd> ast;int top;
vector<Pr> wm; vector<int>stamp; Pr am[1000];int astamp[1000]={},tick=0;
int intern(string w){auto i=ids.find(w);if(i!=ids.end())return i->second;int id=words.size();ids[w]=id;words.push_back(w);mask.push_back(3);atom.push_back(-1);wm.push_back({0,0,0});stamp.push_back(0);return id;}
Pr join(Pr a,Pr b){return{1+a.lead,max({1+a.lead,a.run,b.run}),1+max(a.depth,b.depth)};}
Pr ap(int,map<int,AB>const&);Pr wp(int w,map<int,AB>const&r){if(stamp[w]==tick)return wm[w];Pr p;if(words[w].size()==1)p=ap(atom[w],r);else{auto i=r.find(w);auto ab=i==r.end()?oldrules.at(w):i->second;p=join(wp(ab.first,r),wp(ab.second,r));}stamp[w]=tick;return wm[w]=p;}
Pr ap(int i,map<int,AB>const&r){if(astamp[i]==tick)return am[i];auto z=ast[i];Pr p;if(z.tag=='L')p={0,0,0};else if(z.tag=='W')p=wp(z.a,r);else p=join(ap(z.a,r),ap(z.b,r));astamp[i]=tick;return am[i]=p;}
bool valid(map<int,AB>const&r,Pr &p){
 for(auto[w,b,t]:locks){auto i=r.find(w);if(i==r.end()||(b?i->second.second:i->second.first)!=t)return false;}
 for(auto[w,bits,t]:cons){for(char b:bits){auto i=r.find(w);if(i==r.end())return false;w=b=='1'?i->second.second:i->second.first;}if(w!=t)return false;}
 for(auto[w,ab]:r){int a=ab.first,b=ab.second;if(words[a].size()==1&&!(mask[a]&1))return false;if(words[b].size()==1&&!(mask[b]&2))return false;}
 ++tick;p=ap(top,r);return p.run<=6&&p.depth<=64;
}
void visit(int w,map<int,AB>const&r,set<int>&v){if(words[w].size()==1||v.count(w))return;v.insert(w);auto ab=r.at(w);visit(ab.first,r,v);visit(ab.second,r,v);}
void prune(map<int,AB>&r){set<int>v;for(int w:roots)visit(w,r,v);for(auto i=r.begin();i!=r.end();)if(!v.count(i->first))i=r.erase(i);else++i;}
void save(map<int,AB>const&r,string out){ofstream f(out);for(auto[w,ab]:r)f<<words[w]<<" "<<words[ab.first]<<" "<<words[ab.second]<<"\n";}
int main(int argc,char**argv){ifstream f(argv[1]);int n;f>>n;for(int k=0;k<n;k++){string w;int m,a;f>>w>>m>>a;int i=intern(w);mask[i]=m;atom[i]=a;}f>>n;for(int k=0;k<n;k++){int w,a,b;f>>w>>a>>b;oldrules[w]={a,b};}f>>n;for(int k=0;k<n;k++){int w,a,b;f>>w>>a>>b;baseline[w]={a,b};}f>>n;for(int k=0;k<n;k++){int w;f>>w;roots.push_back(w);}f>>n;for(int k=0;k<n;k++){int w,b,t;f>>w>>b>>t;locks.push_back({w,b,t});}f>>n;for(int k=0;k<n;k++){int w,t;string b;f>>w>>b>>t;cons.push_back({w,b,t});}f>>n>>top;for(int k=0;k<n;k++){Nd d;f>>d.tag>>d.a>>d.b;ast.push_back(d);}
 if(argc>5 && string(argv[5])=="relax")locks.clear();
 int seconds=argc>2?atoi(argv[2]):300,seed=argc>3?atoi(argv[3]):1;string out=argc>4?argv[4]:"search.best";mt19937_64 rng(seed);auto cur=baseline,best=baseline;Pr pp;assert(valid(cur,pp));cerr<<"BASE "<<cur.size()<<" "<<pp.lead<<","<<pp.run<<","<<pp.depth<<endl;set<int>locked;for(auto[w,b,t]:locks)locked.insert(w);
 auto start=chrono::steady_clock::now();long long it=0,acc=0;double elapsed=0;int lastcycle=-1;
 while((elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count())<seconds){++it;int cycle=int(elapsed/20);if(cycle!=lastcycle){cur=best;lastcycle=cycle;}auto itx=cur.begin();advance(itx,rng()%cur.size());int x=itx->first,a=itx->second.first,b=itx->second.second;if(locked.count(x))continue;auto trial=cur;int typ=rng()%5;int fresh=-1;AB newab,child;
 if(typ<2){auto i=cur.find(a);if(i==cur.end())continue;auto[u,v]=i->second;fresh=intern(words[v]+words[b]);newab={u,fresh};child={v,b};}
 else if(typ<4){auto i=cur.find(b);if(i==cur.end())continue;auto[u,v]=i->second;fresh=intern(words[a]+words[u]);newab={fresh,v};child={a,u};}
 else{int k=1+rng()%(words[x].size()-1);auto ai=ids.find(words[x].substr(0,k)),bi=ids.find(words[x].substr(k));if(ai==ids.end()||bi==ids.end())continue;int u=ai->second,v=bi->second;if((words[u].size()>1&&!cur.count(u))||(words[v].size()>1&&!cur.count(v)))continue;newab={u,v};}
 trial[x]=newab;if(fresh>=0&&!trial.count(fresh))trial[fresh]=child;
 if(!valid(trial,pp))continue;prune(trial);int delta=int(trial.size())-int(cur.size());double temp=0.04+0.30*(1-fmod(elapsed,20.0)/20.0);double U=(rng()>>11)*0x1.0p-53;if(delta>0&&U>exp(-delta/temp))continue;cur=move(trial);++acc;
 if(cur.size()<best.size()){best=cur;save(best,out);cerr<<"BEST "<<best.size()<<" it="<<it<<" acc="<<acc<<" time="<<elapsed<<" props="<<pp.lead<<","<<pp.run<<","<<pp.depth<<endl;if(best.size()<=127)break;}
 if(it%1000000==0)cerr<<"PROGRESS "<<it<<" acc="<<acc<<" size="<<cur.size()<<" time="<<elapsed<<" words="<<words.size()<<endl;
 }
 save(best,out);cerr<<"DONE "<<it<<" acc="<<acc<<" best="<<best.size()<<" time="<<elapsed<<" words="<<words.size()<<endl;
}
