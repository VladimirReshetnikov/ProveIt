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

using Tape=std::array<uint64_t,8>;
struct Row { int w,d,t; };
using Table=std::array<std::array<Row,2>,256>;
struct Case { bool halt;int head;Tape initial{},target{}; std::bitset<512> used;int steps; };
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}

bool execute(const Table&T, Case &c, int start,int finish,int fuel,bool record=false){
  Tape tape=c.initial;int h=64,q=start;
  for(int step=1;step<=fuel;step++){
    if(h<0||h>=512)return false;
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
  std::ofstream out("merge-survivors.txt");
  for(size_t ai=0;ai<states.size();ai++)for(size_t bi=ai+1;bi<states.size();bi++){
    int a=states[ai],b=states[bi];
    std::vector<int>quick;
    for(int q:{a,b})for(int bit:{0,1})for(int idx:probes[q*2+bit])if(std::find(quick.begin(),quick.end(),idx)==quick.end())quick.push_back(idx);
    for(int mask=0;mask<4;mask++){
      Table T=old;for(int bit=0;bit<2;bit++)T[a][bit]=old[(mask&(1<<bit))?b:a][bit];
      for(int q:states)if(q!=b)for(int bit=0;bit<2;bit++)if(T[q][bit].t==b)T[q][bit].t=a;
      int dispatcher=96==b?a:96;bool good=true;tested++;
      for(int idx:quick)if(!execute(T,cs[idx],dispatcher,dispatcher,20000)){good=false;break;}
      if(!good)continue;
      full++;
      for(int idx:order)if((cs[idx].used[a*2]||cs[idx].used[a*2+1]||cs[idx].used[b*2]||cs[idx].used[b*2+1])&&!execute(T,cs[idx],dispatcher,dispatcher,20000)){good=false;break;}
      if(good){success++;out<<a<<" "<<b<<" "<<mask<<"\n";out.flush();std::cerr<<"SURVIVOR "<<a<<" "<<b<<" "<<mask<<"\n";}
    }
    if(tested%10000==0)std::cerr<<"done "<<tested<<" full "<<full<<" survivors "<<success<<"\n";
  }
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::cerr<<"FINISH candidates "<<tested<<" full "<<full<<" survivors "<<success<<" seconds "<<seconds<<"\n";
  std::ofstream summary("merge-search-summary.json");summary<<"{\"candidate_count\":"<<tested<<",\"full_literal_pass_count\":"<<success<<",\"past_probes_count\":"<<full<<",\"instruction_cases\":"<<nc<<",\"maximum_baseline_steps\":"<<maximum<<",\"baseline_pairs_exercised\":"<<all.count()<<",\"fuel_per_case\":20000,\"tape_min\":-64,\"tape_max\":447,\"seconds\":"<<seconds<<",\"finite_only\":true}\n";
}
