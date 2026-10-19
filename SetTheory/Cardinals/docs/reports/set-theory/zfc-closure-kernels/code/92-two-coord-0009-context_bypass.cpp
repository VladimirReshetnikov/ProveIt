// Finite context-split state deletion, not a universal correctness proof.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <string>
#include <vector>
using Tape=std::array<uint64_t,32>;
struct Row{int w,d,t;};using Table=std::array<std::array<Row,2>,256>;
struct Case{bool halt;int head;Tape initial{},target{};std::bitset<512>used;};
bool get(const Tape&t,int h){return(t[h>>6]>>(h&63))&1;}
void put(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
constexpr int R=31,K=96,MAX_CONTEXTS=128;
struct Snap{int q,h;uint64_t word;};struct Context{uint64_t word;std::vector<Snap>baseline;};
std::array<std::set<uint64_t>,512>windows;std::array<std::vector<Context>,512>contexts;
void record_context(const Tape&t,int h,int edge){if(h<R||h>=2048-R)return;uint64_t w=0;for(int j=-R;j<=R;j++)w|=uint64_t(get(t,h+j))<<(j+R);windows[edge].insert(w);}
bool execute(const Table&T,Case&c,int fuel,bool record=false){Tape tape=c.initial;int h=64,q=96;
 for(int step=1;step<=fuel;step++){if(h<0||h>=2048)return false;int b=get(tape,h);int edge=q*2+b;if(record)c.used.set(edge);Row r=T[q][b];put(tape,h,r.w);h+=r.d;q=r.t;
  if(q==254)return c.halt;if(record)record_context(tape,h,edge);
  if(!c.halt&&q==96&&h==c.head+64&&tape==c.target)return true;
 }return false;}
bool matches(int q,int h,uint64_t word,const std::vector<Snap>&refs,int del){for(auto&r:refs)if(q!=del&&q==r.q&&h==r.h&&word==r.word)return true;return false;}
bool compatible(const Table&T,int del,int host,const Context&ctx){int q=host,h=R;uint64_t word=ctx.word;
 if(matches(q,h,word,ctx.baseline,del))return true;
 for(int k=0;k<K;k++){Row r=T[q][(word>>h)&1];if(r.w)word|=uint64_t(1)<<h;else word&=~(uint64_t(1)<<h);h+=r.d;q=r.t;
  if(matches(q,h,word,ctx.baseline,del))return true;if(q==del||q==254||h<0||h>2*R)return false;
 }return false;}
int main(int argc,char**argv){std::ifstream in(argc>1?argv[1]:"current245-cases.txt");int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}int nc;in>>nc;std::vector<Case>cs(nc);
 for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;put(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;put(c.target,x+64,1);}}
 for(auto&c:cs)if(!execute(old,c,20000,true)){std::cerr<<"BASELINE FAIL\n";return 1;}
 // Include exact baseline blank prefix in context discovery.
 {Tape t{};int q=95,h=128;for(int k=0;k<407915;k++){if(h<R||h>=2048-R){std::cerr<<"BOOT RANGE FAIL\n";return 1;}int b=get(t,h);int edge=q*2+b;Row r=old[q][b];put(t,h,r.w);h+=r.d;q=r.t;if(q==254){std::cerr<<"BOOT HALT FAIL\n";return 1;}record_context(t,h,edge);}}
 long total=0,samples=0;for(int p:states)for(int b=0;b<2;b++){int edge=p*2+b;int start=old[p][b].t;if(start==254)continue;std::vector<uint64_t>ws(windows[edge].begin(),windows[edge].end());total+=ws.size();std::mt19937 rng(82973+edge);std::shuffle(ws.begin(),ws.end(),rng);if(ws.size()>MAX_CONTEXTS)ws.resize(MAX_CONTEXTS);samples+=ws.size();
  for(auto w:ws){Context c{w,{}};int q=start,h=R;uint64_t word=w;for(int k=0;k<K;k++){Row r=old[q][(word>>h)&1];if(r.w)word|=uint64_t(1)<<h;else word&=~(uint64_t(1)<<h);h+=r.d;q=r.t;c.baseline.push_back({q,h,word});if(q==254||h<0||h>2*R)break;}contexts[edge].push_back(std::move(c));}
 }
 std::cerr<<"CONTEXTS "<<total<<" sampled "<<samples<<"\n";auto began=std::chrono::steady_clock::now();std::ofstream out("context-bypass-survivors.txt");long choices=0,eligible=0,full=0;
 for(int del:states){if(del==95||del==96)continue;std::vector<std::pair<int,std::vector<int>>> routes;bool viable=true;
  for(int p:states)if(p!=del)for(int b=0;b<2;b++)if(old[p][b].t==del){int edge=p*2+b;std::vector<int>hosts;for(int h:states)if(h!=del){choices++;bool good=true;for(auto&c:contexts[edge])if(!compatible(old,del,h,c)){good=false;break;}if(good)hosts.push_back(h);}if(hosts.empty()){viable=false;break;}routes.push_back({edge,hosts});}
  if(!viable||routes.empty())continue;eligible++;Table T=old;for(auto&pr:routes)T[pr.first/2][pr.first%2].t=pr.second[0];bool good=true;for(auto&c:cs)if(c.used[del*2]||c.used[del*2+1])if(!execute(T,c,50000)){good=false;break;}
  std::cerr<<"ELIGIBLE "<<del<<" routes "<<routes.size()<<" full "<<good<<"\n";
  if(good){full++;out<<"DELETE "<<del<<"\n";for(auto&pr:routes){out<<pr.first/2<<' '<<pr.first%2<<" ->";for(int h:pr.second)out<<' '<<h;out<<'\n';}out.flush();std::ofstream tm("bypass"+std::to_string(del)+".tm");tm<<"#! start 95\n";for(int q:states)if(q!=del)for(int b=0;b<2;b++){Row r=T[q][b];tm<<q<<' '<<b<<' '<<r.w<<' '<<(r.d<0?'L':'R')<<' '<<r.t<<'\n';}}
 }
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();std::cerr<<"FINISH choices "<<choices<<" eligible "<<eligible<<" full "<<full<<" seconds "<<sec<<"\n";
 std::ofstream summary("context-bypass-summary.json");summary<<"{\"host_choices\":"<<choices<<",\"eligible_deletions\":"<<eligible<<",\"full_survivors\":"<<full<<",\"contexts\":"<<total<<",\"sampled_contexts\":"<<samples<<",\"radius\":"<<R<<",\"local_steps\":"<<K<<",\"finite_only\":true,\"seconds\":"<<sec<<"}\n";
}
