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
struct Group{vector<pair<string,int>> targets;};vector<Group> groups;vector<int> baseroutes;
bool matches(int w,Group const&g,map<int,AB>const&r){for(auto [bits,t]:g.targets){int z=w;for(char b:bits){auto i=r.find(z);if(i==r.end())return false;z=b=='1'?i->second.second:i->second.first;}if(z!=t)return false;}return true;}
bool valid(map<int,AB>const&r,vector<int>&routes,Pr &p,mt19937_64&rng){
 for(auto[w,b,t]:locks){auto i=r.find(w);if(i==r.end()||(b?i->second.second:i->second.first)!=t)return false;}
 for(int g=0;g<int(groups.size());g++){if(matches(routes[g],groups[g],r))continue;vector<int>choices;for(auto[w,ab]:r)if(matches(w,groups[g],r))choices.push_back(w);if(choices.empty())return false;routes[g]=choices[rng()%choices.size()];}
 for(auto[w,ab]:r){int a=ab.first,b=ab.second;if(words[a].size()==1&&!(mask[a]&1))return false;if(words[b].size()==1&&!(mask[b]&2))return false;}
 ++tick;p=ap(top,r);return p.run<=6&&p.depth<=64;
}
void visit(int w,map<int,AB>const&r,set<int>&v){if(words[w].size()==1||v.count(w))return;v.insert(w);auto ab=r.at(w);visit(ab.first,r,v);visit(ab.second,r,v);}
void prune(map<int,AB>&r,vector<int>const&routes){set<int>v;for(int w:roots)visit(w,r,v);for(int w:routes)visit(w,r,v);for(auto i=r.begin();i!=r.end();)if(!v.count(i->first))i=r.erase(i);else++i;}
void save(map<int,AB>const&r,vector<int>const&routes,string out){ofstream f(out);f<<r.size()<<"\n";for(auto[w,ab]:r)f<<words[w]<<" "<<words[ab.first]<<" "<<words[ab.second]<<"\n";for(int w:routes)f<<words[w]<<"\n";}
int child(Group const&g,map<int,AB>&r,vector<int>const&pool,mt19937_64&rng){for(auto[bits,t]:g.targets)if(bits.empty())return matches(t,g,r)?t:-1;vector<int>ok;for(int w:pool)if(matches(w,g,r))ok.push_back(w);if(!ok.empty()&&rng()%4)return ok[rng()%ok.size()];int f[2]={-1,-1};for(auto[bits,t]:g.targets){if(bits.size()!=1)return -1;int k=bits[0]-'0';if(f[k]>=0&&f[k]!=t)return -1;f[k]=t;}for(int k=0;k<20;k++){int a=f[0]>=0?f[0]:pool[rng()%pool.size()],b=f[1]>=0?f[1]:pool[rng()%pool.size()];if(words[a].size()+words[b].size()>90)continue;if(words[a].size()==1&&!(mask[a]&1))continue;if(words[b].size()==1&&!(mask[b]&2))continue;int w=intern(words[a]+words[b]);if(r.count(w)&&r[w]!=AB(a,b))continue;r[w]={a,b};return w;}return -1;}
int main(int argc,char**argv){ifstream f(argv[1]);int n;f>>n;for(int k=0;k<n;k++){string w;int m,a;f>>w>>m>>a;int i=intern(w);mask[i]=m;atom[i]=a;}f>>n;for(int k=0;k<n;k++){int w,a,b;f>>w>>a>>b;oldrules[w]={a,b};}f>>n;for(int k=0;k<n;k++){int w,a,b;f>>w>>a>>b;baseline[w]={a,b};}f>>n;for(int k=0;k<n;k++){int w;f>>w;roots.push_back(w);}f>>n;for(int k=0;k<n;k++){int w,b,t;f>>w>>b>>t;locks.push_back({w,b,t});}f>>n;for(int k=0;k<n;k++){int w,m;f>>w>>m;baseroutes.push_back(w);Group g;for(int j=0;j<m;j++){string bits;int tar;f>>bits>>tar;g.targets.push_back({bits,tar});}groups.push_back(g);}f>>n>>top;for(int k=0;k<n;k++){Nd d;f>>d.tag>>d.a>>d.b;ast.push_back(d);}
 if(argc>5&&string(argv[5])=="relax")locks.clear();
 int seconds=argc>2?atoi(argv[2]):300,seed=argc>3?atoi(argv[3]):1;string out=argc>4?argv[4]:"joint.best";mt19937_64 rng(seed);auto cur=baseline,best=baseline;auto rt=baseroutes,brt=baseroutes;Pr pp;assert(valid(cur,rt,pp,rng));cerr<<"BASE "<<cur.size()<<" "<<pp.lead<<","<<pp.run<<","<<pp.depth<<endl;set<int>locked;for(auto[w,b,t]:locks)locked.insert(w);
 auto start=chrono::steady_clock::now();long long it=0,acc=0;double elapsed=0,nextlog=30;int lastcycle=-1;
 while((elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count())<seconds){++it;int cycle=int(elapsed/30);if(cycle!=lastcycle){cur=best;rt=brt;lastcycle=cycle;}auto trial=cur;auto trt=rt;int typ=rng()%100;bool changed=true;
 if(typ<85){auto itx=cur.begin();advance(itx,rng()%cur.size());int x=itx->first,a=itx->second.first,b=itx->second.second;if(locked.count(x))continue;int fresh=-1;AB ab,ch;
 if(typ<32){auto i=cur.find(a);if(i==cur.end())continue;auto[u,v]=i->second;fresh=intern(words[v]+words[b]);ab={u,fresh};ch={v,b};}
 else if(typ<65){auto i=cur.find(b);if(i==cur.end())continue;auto[u,v]=i->second;fresh=intern(words[a]+words[u]);ab={fresh,v};ch={a,u};}
 else{vector<AB>opts;for(int k=1;k<int(words[x].size());k++){auto ai=ids.find(words[x].substr(0,k)),bi=ids.find(words[x].substr(k));if(ai==ids.end()||bi==ids.end())continue;int u=ai->second,v=bi->second;if((words[u].size()>1&&!cur.count(u))||(words[v].size()>1&&!cur.count(v)))continue;opts.push_back({u,v});}if(opts.empty())continue;ab=opts[rng()%opts.size()];}
 trial[x]=ab;if(fresh>=0&&!trial.count(fresh))trial[fresh]=ch;
 }else if(typ<90){int g=rng()%groups.size();vector<int>opts;for(auto[w,ab]:trial)if(matches(w,groups[g],trial))opts.push_back(w);if(opts.empty())continue;trt[g]=opts[rng()%opts.size()];}
 else{int g=rng()%groups.size();Group c[2];for(auto[bits,t]:groups[g].targets)c[bits[0]-'0'].targets.push_back({bits.substr(1),t});vector<int>pool;for(auto[w,ab]:trial)pool.push_back(w);for(int w=0;w<int(words.size());w++)if(words[w].size()==1)pool.push_back(w);int a=child(c[0],trial,pool,rng),b=child(c[1],trial,pool,rng);if(a<0||b<0)continue;if(words[a].size()+words[b].size()>180)continue;int w=intern(words[a]+words[b]);if(trial.count(w)&&trial[w]!=AB(a,b))continue;trial[w]={a,b};trt[g]=w;}
 if(!valid(trial,trt,pp,rng))continue;prune(trial,trt);int delta=int(trial.size())-int(cur.size());double temp=0.08+0.42*(1-fmod(elapsed,30.0)/30.0);double U=(rng()>>11)*0x1.0p-53;if(trial.size()>best.size()+5||(delta>0&&U>exp(-delta/temp)))continue;cur=move(trial);rt=move(trt);++acc;
 if(cur.size()==best.size()&&rng()%100==0){best=cur;brt=rt;}
 if(cur.size()<best.size()){best=cur;brt=rt;save(best,brt,out);cerr<<"BEST "<<best.size()<<" it="<<it<<" acc="<<acc<<" time="<<elapsed<<" props="<<pp.lead<<","<<pp.run<<","<<pp.depth<<endl;if(best.size()<=127)break;}
 if(elapsed>=nextlog){cerr<<"PROGRESS "<<it<<" acc="<<acc<<" size="<<cur.size()<<" time="<<elapsed<<" words="<<words.size()<<endl;nextlog+=30;}
 }
 save(best,brt,out);cerr<<"DONE "<<it<<" acc="<<acc<<" best="<<best.size()<<" time="<<elapsed<<" words="<<words.size()<<endl;
}
