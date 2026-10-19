// Adapted from ProveIt incoming beyond246 merge_search.cpp. Original algorithm credited in NOTICE.
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
struct Case { bool halt;int head;Tape initial{},target{}; std::bitset<512> used;int steps; };
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}

bool execute(const Table&T, Case &c, int start,int finish,int fuel,bool record=false){
  Tape tape=c.initial;int h=64,q=start;
  for(int step=1;step<=fuel;step++){
    if(h<0||h>=2048)return false;
    int b=get(tape,h);if(record)c.used.set(q*2+b);
    Row row=T[q][b];set(tape,h,row.w);h+=row.d;q=row.t;
    if(q==254){if(record)c.steps=step;return c.halt;}
    if(!c.halt&&q==finish&&h==c.head+64&&tape==c.target){if(record)c.steps=step;return true;}
  }
  return false;
}

int main(int argc,char**argv){
  std::ifstream in(argc>1?argv[1]:"merge-cases.txt");int nr;in>>nr;
  Table old{};std::vector<int>states;
  for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
  int nc;in>>nc;std::vector<Case>cs(nc);
  for(auto &c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
  int maximum=0;std::bitset<512>all;
  for(auto &c:cs){if(!execute(old,c,96,96,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}maximum=std::max(maximum,c.steps);all|=c.used;}
  std::cerr<<"Baseline "<<nc<<" cases maxsteps "<<maximum<<" pairs "<<all.count()<<"\n";
  std::array<std::vector<int>,512>probes;
  std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;
  std::mt19937 rng(20261018);std::shuffle(order.begin(),order.end(),rng);
  for(int k=0;k<512;k++)for(int idx:order)if(cs[idx].used[k]){probes[k].push_back(idx);if(probes[k].size()>=5)break;}
  auto began=std::chrono::steady_clock::now();int tested=0,full=0,success=0;
  std::ofstream out("eliminate-survivors.txt"); std::ofstream near("near-eliminations.txt");
  for(int eliminated:states){
    if(eliminated==95||eliminated==96)continue;
    std::vector<std::pair<int,int>> incoming;
    for(int q:states)if(q!=eliminated)for(int bit:{0,1})if(old[q][bit].t==eliminated)incoming.push_back({q,bit});
    if(incoming.size()!=1)continue;
    auto [pre,read]=incoming[0];
    std::vector<int>quick;
    for(int q:{eliminated,pre})for(int bit:{0,1})for(int idx:probes[q*2+bit])if(std::find(quick.begin(),quick.end(),idx)==quick.end())quick.push_back(idx);
    for(int target:states)if(target!=eliminated)for(int write:{0,1})for(int direction:{-1,1}){
      Table T=old;T[pre][read]={write,direction,target};
      bool good=true;tested++;
      for(int idx:quick)if(!execute(T,cs[idx],96,96,20000)){good=false;break;}
      if(!good)continue;full++;
      for(int idx:order)if((cs[idx].used[eliminated*2]||cs[idx].used[eliminated*2+1]||cs[idx].used[pre*2+read])&&!execute(T,cs[idx],96,96,20000)){good=false;near<<eliminated<<" "<<pre<<" "<<read<<" "<<write<<" "<<direction<<" "<<target<<" "<<idx<<"\n";break;}
      if(good){success++;out<<eliminated<<" "<<pre<<" "<<read<<" "<<write<<" "<<direction<<" "<<target<<"\n";out.flush();std::cerr<<"SURVIVOR "<<eliminated<<" via "<<pre<<" "<<read<<" => "<<write<<" "<<direction<<" "<<target<<"\n";}
    }
    std::cerr<<"eliminated "<<eliminated<<" done "<<tested<<" full "<<full<<" survivors "<<success<<"\n";
  }
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::cerr<<"FINISH candidates "<<tested<<" full "<<full<<" survivors "<<success<<" seconds "<<seconds<<"\n";
  std::ofstream summary("eliminate-search-summary.json");summary<<"{\"candidate_count\":"<<tested<<",\"full_literal_pass_count\":"<<success<<",\"past_probes_count\":"<<full<<",\"instruction_cases\":"<<nc<<",\"maximum_baseline_steps\":"<<maximum<<",\"baseline_pairs_exercised\":"<<all.count()<<",\"fuel_per_case\":20000,\"tape_min\":-64,\"tape_max\":1983,\"seconds\":"<<seconds<<",\"finite_only\":true}\n";
}
