// Search separable two-entry-state deletions with independently synthesized incoming rows.
// Simulator representation adapted from attributed zfc245-proof package's
// check_literal_cases.cpp, itself derived from ProveIt beyond246 merge_search.cpp.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>
using Tape=std::array<uint64_t,32>;
struct Row { int w,d,t; };
using Table=std::array<std::array<Row,2>,256>;
struct Case { bool halt;int head;Tape initial{},target{};std::bitset<512> used;int steps; };
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
bool execute(const Table&T,Case&c,int deleted,int fuel,bool record=false){
 Tape tape=c.initial;int h=64,q=96;
 for(int step=1;step<=fuel;step++){
  if(h<0||h>=2048||q==deleted)return false;
  int b=get(tape,h);if(record)c.used.set(q*2+b);
  Row row=T[q][b];set(tape,h,row.w);h+=row.d;q=row.t;
  if(q==254){if(record)c.steps=step;return c.halt;}
  if(!c.halt&&q==96&&h==c.head+64&&tape==c.target){if(record)c.steps=step;return true;}
 }
 return false;
}
int main(int argc,char**argv){
 std::ifstream in(argv[1]);int nr;in>>nr;Table old{};std::vector<int> states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cs(nc);
 for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
 int maximum=0;std::bitset<512>all;for(auto&c:cs){if(!execute(old,c,-1,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}maximum=std::max(maximum,c.steps);all|=c.used;}
 std::cerr<<"Baseline "<<nc<<" cases maxsteps "<<maximum<<" pairs "<<all.count()<<"\n";
 std::array<std::vector<std::pair<int,int>>,256>incoming;
 for(int q:states)for(int b:{0,1})if(old[q][b].t!=q)incoming[old[q][b].t].push_back({q,b});
 std::vector<int> order(nc);for(int i=0;i<nc;i++)order[i]=i;std::mt19937 rng(20261019);std::shuffle(order.begin(),order.end(),rng);
 auto began=std::chrono::steady_clock::now();long long tested=0,full=0,locals=0,combinations=0,success=0,unique=0,emptyedges=0;
 std::ofstream out("two-incoming-survivors.txt"),ledger("two-incoming-local-candidates.txt");
 for(int deleted:states){
  if(deleted==95||deleted==96||incoming[deleted].size()!=2)continue;unique++;
  std::array<std::vector<Row>,2> passing;
  for(int edge=0;edge<2;edge++){
   auto [p,b]=incoming[deleted][edge];std::vector<int> quick,relevant;
   for(int idx:order)if(cs[idx].used[p*2+b]){relevant.push_back(idx);if(quick.size()<8)quick.push_back(idx);}
   for(int w:{0,1})for(int d:{-1,1})for(int target:states){
    if(target==deleted)continue;Table t=old;t[p][b]={w,d,target};tested++;
    bool good=true;for(int idx:quick)if(!execute(t,cs[idx],-1,20000)){good=false;break;}
    if(!good)continue;full++;for(int idx:relevant)if(!execute(t,cs[idx],-1,20000)){good=false;break;}
    if(good){locals++;passing[edge].push_back({w,d,target});ledger<<deleted<<" "<<edge<<" "<<p<<" "<<b<<" "<<w<<" "<<d<<" "<<target<<"\n";}
   }
   if(passing[edge].empty())emptyedges++;
  }
  for(Row a:passing[0])for(Row b:passing[1]){
   combinations++;Table t=old;auto[e0,b0]=incoming[deleted][0];auto[e1,b1]=incoming[deleted][1];t[e0][b0]=a;t[e1][b1]=b;
   bool good=true;for(int idx:order)if(!execute(t,cs[idx],deleted,20000)){good=false;break;}
   if(good){success++;out<<deleted<<" "<<e0<<" "<<b0<<" "<<a.w<<" "<<a.d<<" "<<a.t<<" "<<e1<<" "<<b1<<" "<<b.w<<" "<<b.d<<" "<<b.t<<"\n";out.flush();std::cerr<<"SURVIVOR "<<deleted<<"\n";}
  }
  std::cerr<<"deleted "<<deleted<<" local sizes "<<passing[0].size()<<","<<passing[1].size()<<" candidates "<<tested<<" full "<<full<<" combined "<<combinations<<" survivors "<<success<<"\n";
 }
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 std::ofstream summary("two-incoming-summary.json");summary<<"{\"local_candidate_count\":"<<tested<<",\"two_entry_states\":"<<unique<<",\"empty_local_edges\":"<<emptyedges<<",\"local_survivors\":"<<locals<<",\"full_literal_survivors\":"<<success<<",\"combinations_tested\":"<<combinations<<",\"past_probes_count\":"<<full<<",\"instruction_cases\":"<<nc<<",\"maximum_baseline_steps\":"<<maximum<<",\"baseline_pairs_exercised\":"<<all.count()<<",\"fuel_per_case\":20000,\"tape_min\":-64,\"tape_max\":1983,\"seconds\":"<<sec<<",\"finite_only\":true,\"separable_local_replacements_only\":true}\n";
 std::cout<<"finished local "<<tested<<" combinations "<<combinations<<" survivors "<<success<<" seconds "<<sec<<"\n";
}
