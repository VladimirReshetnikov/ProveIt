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
  std::ifstream in(argc>1?argv[1]:"candidate245-literal-cases.txt");int nr;in>>nr;
  Table old{};std::vector<int>states;
  for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
  int nc;in>>nc;std::vector<Case>cs(nc);
  for(auto &c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
  for(auto &c:cs)if(!execute(old,c,96,96,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}
  std::array<std::vector<int>,512>allcases;
  std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;
  std::mt19937 rng(12461018);std::shuffle(order.begin(),order.end(),rng);
  for(int k=0;k<512;k++)for(int idx:order)if(cs[idx].used[k])allcases[k].push_back(idx);
  std::ofstream out("edge-reroute-survivors.txt");
  auto began=std::chrono::steady_clock::now();int tested=0,full=0,success=0;
  for(int source:states)for(int bit:{0,1}){
    int original=old[source][bit].t;
    if(original==254)continue;
    for(int target:states){
      if(target==original)continue;
      Table T=old;T[source][bit].t=target;
      bool good=true;tested++;int index=0;
      for(int ci:allcases[source*2+bit]){
        if(!execute(T,cs[ci],96,96,20000)){good=false;break;}
        index++;if(index==5)full++;
      }
      if(good){success++;out<<source<<" "<<bit<<" "<<original<<" "<<target<<"\n";out.flush();std::cerr<<"SURVIVOR "<<source<<"/"<<bit<<" "<<original<<" -> "<<target<<"\n";}
    }
  }
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::cerr<<"FINISH candidates "<<tested<<" full "<<full<<" survivors "<<success<<" seconds "<<seconds<<"\n";
  std::ofstream summary("edge-reroute-summary.json");summary<<"{\"candidate_count\":"<<tested<<",\"full_literal_pass_count\":"<<success<<",\"past_probes_count\":"<<full<<",\"instruction_cases\":"<<nc<<",\"fuel_per_case\":20000,\"tape_min\":-64,\"tape_max\":1983,\"seconds\":"<<seconds<<",\"finite_only\":true}\n";
}
