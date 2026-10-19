// New bounded family: merge two states having one identical row modulo the
// quotient, and freely synthesize the other row. Neither input row need survive.
// Simulator shape adapted from attributed ProveIt check_literal_cases.cpp.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using Tape=std::array<uint64_t,32>;
struct Row{int w,d,t;};
using Table=std::array<std::array<Row,2>,256>;
struct Case{bool halt;int head;Tape initial{},target{};std::bitset<512> used;int steps;};
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,int b){uint64_t v=uint64_t(1)<<(h&63);if(b)t[h>>6]|=v;else t[h>>6]&=~v;}
bool run(const Table&t,Case&c,int fuel,bool record=false){
 Tape a=c.initial;int h=64,q=96;
 for(int k=1;k<=fuel;k++){
  if(h<0||h>=2048)return false;
  int b=get(a,h);if(record)c.used.set(q*2+b);
  Row r=t[q][b];set(a,h,r.w);h+=r.d;q=r.t;
  if(q==254){if(record)c.steps=k;return c.halt;}
  if(!c.halt&&q==96&&h==c.head+64&&a==c.target){if(record)c.steps=k;return true;}
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=2)return 2;
 std::ifstream in(argv[1]);int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cs(nc);
 for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int i=0;i<n;i++){in>>x;set(c.initial,x+64,1);}in>>n;for(int i=0;i<n;i++){in>>x;set(c.target,x+64,1);}}
 int maxsteps=0;std::bitset<512>all;
 for(auto&c:cs){if(!run(old,c,20000,true)){std::cerr<<"baseline failed\n";return 1;}maxsteps=std::max(maxsteps,c.steps);all|=c.used;}
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;std::mt19937 rng(4101817);std::shuffle(order.begin(),order.end(),rng);
 auto start=std::chrono::steady_clock::now();int pairs=0,tests=0,full=0,success=0;
 std::ofstream survivors("shared-row-survivors.txt");
 for(int a:states)for(int b:states){
  if(a>=b||a==96||b==96)continue;
  auto canon=[&](Row r){if(r.t==b)r.t=a;return r;};
  int common=-1;
  for(int bit:{0,1}){Row x=canon(old[a][bit]),y=canon(old[b][bit]);if(x.w==y.w&&x.d==y.d&&x.t==y.t)common=bit;}
  if(common<0)continue;pairs++;
  Table t=old;for(int q:states)if(q!=b)for(int bit:{0,1})t[q][bit]=canon(t[q][bit]);
  std::vector<int>quick,relevant;
  std::array<int,4>count{};
  for(int ix:order)if(cs[ix].used[a*2]||cs[ix].used[a*2+1]||cs[ix].used[b*2]||cs[ix].used[b*2+1]){
   relevant.push_back(ix);bool add=false;
   for(int qn:{0,1})for(int bit:{0,1})if(cs[ix].used[(qn?b:a)*2+bit]&&count[qn*2+bit]<4){count[qn*2+bit]++;add=true;}
   if(add)quick.push_back(ix);
  }
  std::vector<int>targets=states;targets.push_back(254);
  for(int w:{0,1})for(int d:{-1,1})for(int target:targets){
   if(target==b)continue;t[a][1-common]={w,d,target};tests++;
   bool good=true;for(int ix:quick)if(!run(t,cs[ix],20000)){good=false;break;}
   if(!good)continue;full++;
   for(int ix:relevant)if(!run(t,cs[ix],20000)){good=false;break;}
   if(good){success++;survivors<<a<<" "<<b<<" "<<common<<" "<<w<<" "<<d<<" "<<target<<"\n";survivors.flush();std::cerr<<"SURVIVOR "<<a<<" "<<b<<" "<<common<<" "<<w<<" "<<d<<" "<<target<<"\n";}
  }
  if(pairs%20==0)std::cerr<<"pairs "<<pairs<<" tests "<<tests<<" full "<<full<<" survivors "<<success<<"\n";
 }
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::ofstream report("shared-row-summary.json");report<<"{\"pairs\":"<<pairs<<",\"tables_tested\":"<<tests<<",\"past_probes\":"<<full<<",\"survivors\":"<<success<<",\"cases\":"<<nc<<",\"maximum_baseline_steps\":"<<maxsteps<<",\"row_coverage\":"<<all.count()<<",\"fuel\":20000,\"seconds\":"<<sec<<",\"finite_only\":true}\n";
 std::cerr<<"finished "<<sec<<" seconds\n";
}
