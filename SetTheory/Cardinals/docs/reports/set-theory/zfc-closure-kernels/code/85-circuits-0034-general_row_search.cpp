// Optional incomplete broader search. See README; no exhaustive conclusion.
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
  std::ifstream in(argc>1?argv[1]:"merge-cases.txt");int nr;in>>nr;
  Table old{};std::vector<int>states;
  for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
  int nc;in>>nc;std::vector<Case>cs(nc);
  for(auto &c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
  int maximum=0;std::bitset<1024>all;
  for(auto &c:cs){if(!execute(old,c,96,96,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}maximum=std::max(maximum,c.steps);all|=c.used;}
  std::cerr<<"Baseline "<<nc<<" cases maxsteps "<<maximum<<" pairs "<<all.count()<<"\n";
  std::array<std::vector<int>,1024>probes;
  std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;
  std::mt19937 rng(20261018);std::shuffle(order.begin(),order.end(),rng);
  for(int k=0;k<1024;k++)for(int idx:order)if(cs[idx].used[k]){probes[k].push_back(idx);if(probes[k].size()>=5)break;}
  auto began=std::chrono::steady_clock::now();long long tested=0,full=0,success=0,pairs=0,families=0,screened=0,skipped=0;bool stop=false;
  double limit=argc>2?std::stod(argv[2]):300;
  std::ofstream out("general-row-survivors.txt");
  auto probe=[&](const Table&T,Case&c,int dispatcher,int freeq,int freebit){
    Tape tape=c.initial;int h=64,q=dispatcher;
    for(int step=1;step<=20000;step++){
      if(h<0||h>=512)return 0;
      int b=get(tape,h);if(q==freeq&&b==freebit)return 2;
      Row row=T[q][b];set(tape,h,row.w);h+=row.d;q=row.t;
      if(q==254)return c.halt?1:0;
      if(!c.halt&&q==dispatcher&&h==c.head+64&&tape==c.target)return 1;
    }
    return 0;
  };
  std::vector<std::pair<int,int>> allpairs;
  for(size_t ai=0;ai<states.size();ai++)for(size_t bi=ai+1;bi<states.size();bi++)allpairs.push_back({states[ai],states[bi]});
  std::shuffle(allpairs.begin(),allpairs.end(),rng);
  for(auto [a,b]:allpairs){
    if(std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()>limit){stop=true;break;}
    auto mapped=[&](Row r){if(r.t==b)r.t=a;return r;};
    auto equal=[](Row x,Row y){return x.w==y.w&&x.d==y.d&&x.t==y.t;};
    pairs++;
    std::vector<int>quick;
    for(int st:{a,b})for(int bit:{0,1})for(int idx:probes[st*2+bit])if(std::find(quick.begin(),quick.end(),idx)==quick.end())quick.push_back(idx);
    Table T=old;for(int st:states)if(st!=b)for(int bit:{0,1})T[st][bit]=mapped(T[st][bit]);
    int dispatcher=96==b?a:96;
    for(int known:{0,1}){
      if(equal(mapped(old[a][known]),mapped(old[b][known])))continue; // Previously completed shared-row family.
      int free=1-known;
      for(int provider:{a,b}){
        T[a][known]=mapped(old[provider][known]);families++;
        bool potential=true;
        for(size_t pos=0;pos<quick.size();pos++)if(probe(T,cs[quick[pos]],dispatcher,a,free)==0){potential=false;std::swap(quick[0],quick[pos]);break;}
        if(!potential){skipped++;continue;}screened++;
        std::vector<int>targets=states;targets.push_back(254);
        for(int wr:{0,1})for(int dr:{-1,1})for(int target:targets){
          if(target==b)continue;
          T[a][free]={wr,dr,target};bool good=true;tested++;
          for(size_t pos=0;pos<quick.size();pos++)if(!execute(T,cs[quick[pos]],dispatcher,dispatcher,20000)){good=false;std::swap(quick[0],quick[pos]);break;}
          if(!good)continue;
          full++;
          for(int idx:order)if((cs[idx].used[a*2]||cs[idx].used[a*2+1]||cs[idx].used[b*2]||cs[idx].used[b*2+1])&&!execute(T,cs[idx],dispatcher,dispatcher,20000)){good=false;break;}
          if(good){success++;out<<a<<" "<<b<<" "<<known<<" "<<provider<<" "<<free<<" "<<wr<<" "<<dr<<" "<<target<<"\n";out.flush();std::cerr<<"SURVIVOR "<<a<<" "<<b<<" "<<free<<" "<<wr<<" "<<dr<<" "<<target<<"\n";
            std::ofstream tm("general-survivor-"+std::to_string(success)+".tm");tm<<"#! start "<<(95==b?a:95)<<"\n";
            for(int st:states)if(st!=b)for(int bit:{0,1}){auto row=T[st][bit];tm<<st<<" "<<bit<<" "<<row.w<<" "<<(row.d==1?"R":"L")<<" "<<row.t<<"\n";}
          }
        }
      }
    }
    if(pairs%1000==0)std::cerr<<"done pairs "<<pairs<<" families "<<families<<" screened "<<screened<<" recipes "<<tested<<" full "<<full<<" survivors "<<success<<"\n";
  }
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::cerr<<"FINISH pairs "<<pairs<<" families "<<families<<" screened "<<screened<<" skipped "<<skipped<<" candidates "<<tested<<" full "<<full<<" survivors "<<success<<" seconds "<<seconds<<" partial "<<stop<<"\n";
  std::ofstream summary("general-row-summary.json");summary<<"{\"pair_count\":"<<pairs<<",\"families_considered\":"<<families<<",\"families_without_free_row_failures\":"<<screened<<",\"families_excluded_by_no_free_row_failure\":"<<skipped<<",\"candidate_count\":"<<tested<<",\"full_literal_pass_count\":"<<success<<",\"past_probes_count\":"<<full<<",\"instruction_cases\":"<<nc<<",\"maximum_baseline_steps\":"<<maximum<<",\"baseline_pairs_exercised\":"<<all.count()<<",\"fuel_per_case\":20000,\"tape_min\":-64,\"tape_max\":447,\"seconds\":"<<seconds<<",\"finite_only\":true,\"partial\":"<<(stop?"true":"false")<<"}\n";
}
