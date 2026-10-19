// Derived from the attributed Context246 pair-merge fixture runner in the
// incoming zfc-beyond246-research-20261018 packet (MIT, ProveIt lineage).
// New search: one quotient row shared exactly; synthesize the OTHER row as
// every write/move/target action. Finite fixture rejection is not a lower bound.
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
using Table=std::array<std::array<Row,2>,512>;
struct Case { bool halt;int head;Tape initial{},target{}; std::bitset<1024> used;int steps; };
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
  std::ifstream file; bool stream=argc>1&&std::string(argv[1])=="-";
  if(!stream)file.open(argc>1?argv[1]:"merge-cases.txt");
  std::istream& in=stream?std::cin:file;int nr=0;
  if(!(in>>nr)||nr!=492){std::cerr<<"Expected 492 transition rows\n";return 2;}
  Table old{};std::vector<int>states;
  for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
  int nc=0;in>>nc;if(nc!=8391&&nc!=8385&&nc!=33540){std::cerr<<"Expected 8391, 8385, or 33540 fixtures\n";return 2;}std::vector<Case>cs(nc);
  for(auto &c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
  if(!in||states.size()!=246){std::cerr<<"Malformed fixture/table input\n";return 2;}
  int maximum=0;std::bitset<1024>all;
  for(auto &c:cs){if(!execute(old,c,96,96,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}maximum=std::max(maximum,c.steps);all|=c.used;}
  std::cerr<<"Baseline "<<nc<<" cases maxsteps "<<maximum<<" pairs "<<all.count()<<"\n";
  std::array<std::vector<int>,1024>probes;
  std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;
  std::mt19937 rng(20261018);std::shuffle(order.begin(),order.end(),rng);
  for(int k=0;k<1024;k++)for(int idx:order)if(cs[idx].used[k]){probes[k].push_back(idx);if(probes[k].size()>=5)break;}
  auto began=std::chrono::steady_clock::now();long long tested=0,full=0,success=0,pairs=0;
  std::ofstream out("arbitrary-row-survivors.txt");
  for(size_t ai=0;ai<states.size();ai++)for(size_t bi=ai+1;bi<states.size();bi++){
    int a=states[ai],b=states[bi];
    auto mapped=[&](Row r){if(r.t==b)r.t=a;return r;};
    auto equal=[](Row x,Row y){return x.w==y.w&&x.d==y.d&&x.t==y.t;};
    int same=-1,differences=0;
    for(int bit:{0,1})if(equal(mapped(old[a][bit]),mapped(old[b][bit])))same=bit;else differences++;
    if(differences!=1)continue;
    pairs++;
    std::vector<int>quick;
    for(int st:{a,b})for(int bit:{0,1})for(int idx:probes[st*2+bit])if(std::find(quick.begin(),quick.end(),idx)==quick.end())quick.push_back(idx);
    Table T=old;for(int st:states)if(st!=b)for(int bit:{0,1})T[st][bit]=mapped(T[st][bit]);
    int dispatcher=96==b?a:96; int change=1-same;
    std::vector<int> targets=states;targets.push_back(254);
    for(int wr:{0,1})for(int dr:{-1,1})for(int target:targets){
      if(target==b)continue;
      T[a][change]={wr,dr,target};bool good=true;tested++;
      for(size_t pos=0;pos<quick.size();pos++)if(!execute(T,cs[quick[pos]],dispatcher,dispatcher,20000)){
        good=false;std::swap(quick[0],quick[pos]);break;
      }
      if(!good)continue;
      full++;
      for(int idx:order)if((cs[idx].used[a*2]||cs[idx].used[a*2+1]||cs[idx].used[b*2]||cs[idx].used[b*2+1])&&!execute(T,cs[idx],dispatcher,dispatcher,20000)){good=false;break;}
      if(good){success++;out<<a<<" "<<b<<" "<<change<<" "<<wr<<" "<<dr<<" "<<target<<"\n";out.flush();std::cerr<<"SURVIVOR "<<a<<" "<<b<<" "<<change<<" "<<wr<<" "<<dr<<" "<<target<<"\n";
        std::ofstream tm("survivor-"+std::to_string(success)+".tm");tm<<"#! start "<<(95==b?a:95)<<"\n";
        for(int st:states)if(st!=b)for(int bit:{0,1}){auto row=T[st][bit];tm<<st<<" "<<bit<<" "<<row.w<<" "<<(row.d==1?"R":"L")<<" "<<row.t<<"\n";}
      }
    }
    if(pairs%20==0)std::cerr<<"done pairs "<<pairs<<" recipes "<<tested<<" full "<<full<<" survivors "<<success<<"\n";
  }
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::cerr<<"FINISH pairs "<<pairs<<" candidates "<<tested<<" full "<<full<<" survivors "<<success<<" seconds "<<seconds<<"\n";
  std::ofstream summary("arbitrary-row-summary.json");summary<<"{\"pair_count\":"<<pairs<<",\"candidate_count\":"<<tested<<",\"full_literal_pass_count\":"<<success<<",\"past_probes_count\":"<<full<<",\"instruction_cases\":"<<nc<<",\"maximum_baseline_steps\":"<<maximum<<",\"baseline_pairs_exercised\":"<<all.count()<<",\"fuel_per_case\":20000,\"tape_min\":-64,\"tape_max\":447,\"seconds\":"<<seconds<<",\"finite_only\":true,\"halt_targets_included\":true}\n";
}
