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


// This intentionally weaker finite screen admits different gap and spare values.
// Survivors require an independent universal proof before any machine claim.
bool semantically_equal(const Tape&t,int head,const Case&c){
  int ehead=c.head+64;
  if(head<1||head>512) return false;
  for(int i=0;i<head-1;i++) if(get(t,i))return false;
  if(!get(t,head-1))return false;
  for(int i=0;i<64;i++)if(get(t,head+i)!=get(c.target,ehead+i))return false;
  int eh=ehead+64;while(eh<2048&&!get(c.target,eh))eh++;
  int th=head+64;while(th<2048&&!get(t,th))th++;
  if(eh==2048||th==2048)return false;
  int ep=eh+1,tp=th+1;
  for(int r=0;r<9;r++){
    if(ep+1>=2048||tp+1>=2048||get(c.target,ep)||get(t,tp)||!get(c.target,ep+1)||!get(t,tp+1))return false;
    ep++;tp++;int ev=0,tv=0;
    while(ep<2048&&get(c.target,ep)){ev++;ep++;}
    while(tp<2048&&get(t,tp)){tv++;tp++;}
    if(ev!=tv)return false;
  }
  int spares=0;
  while(tp+1<2048&&get(t,tp+1)){
    if(get(t,tp))return false;
    tp+=2;
    while(tp<2048&&get(t,tp))tp++;
    spares++;
  }
  if(spares<1)return false;
  for(;tp<2048;tp++)if(get(t,tp))return false;
  return true;
}

bool execute(const Table&T, Case &c, int start,int finish,int fuel,bool record=false,std::bitset<512>* trace=nullptr){
  Tape tape=c.initial;int h=64,q=start;
  for(int step=1;step<=fuel;step++){
    if(h<0||h>=2048)return false;
    int b=get(tape,h);if(record)c.used.set(q*2+b);if(trace)trace->set(q*2+b);
    Row row=T[q][b];set(tape,h,row.w);h+=row.d;q=row.t;
    if(q==254){if(record)c.steps=step;return c.halt;}
    if(!c.halt&&q==finish&&semantically_equal(tape,h,c)){if(record)c.steps=step;return true;}
  }
  return false;
}


int main(int argc,char**argv){
 std::ifstream in(argv[1]);int nr;in>>nr;
 Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cs(nc);
 for(auto &c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
 int maximum=0;std::bitset<512>all;
 for(auto &c:cs){if(!execute(old,c,96,96,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}maximum=std::max(maximum,c.steps);all|=c.used;}
 std::cerr<<"Baseline "<<nc<<" cases maxsteps "<<maximum<<" rows "<<all.count()<<"\n";
 std::array<std::vector<int>,512>probes;
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;
 std::mt19937 rng(20261018);std::shuffle(order.begin(),order.end(),rng);
 for(int k=0;k<512;k++)for(int idx:order)if(cs[idx].used[k]){probes[k].push_back(idx);if(probes[k].size()>=5)break;}
 auto began=std::chrono::steady_clock::now();int merged=0,seed_count=0,success=0;uint64_t repaired=0,first_pass=0,quick_pass=0;
 std::ofstream out("repair_survivors.txt"),seed_out("repair_seeds.txt");
 for(size_t ai=0;ai<states.size();ai++)for(size_t bi=ai+1;bi<states.size();bi++){
  int a=states[ai],b=states[bi];
  std::vector<int>quick;
  for(int q:{a,b})for(int bit:{0,1})for(int idx:probes[q*2+bit])if(std::find(quick.begin(),quick.end(),idx)==quick.end())quick.push_back(idx);
  for(int mask=0;mask<4;mask++){
   Table T=old;for(int bit=0;bit<2;bit++)T[a][bit]=old[(mask&(1<<bit))?b:a][bit];
   for(int q:states)if(q!=b)for(int bit=0;bit<2;bit++)if(T[q][bit].t==b)T[q][bit].t=a;
   int dispatcher=96==b?a:96;bool good=true;merged++;
   for(int idx:quick)if(!execute(T,cs[idx],dispatcher,dispatcher,20000)){good=false;break;}
   if(!good)continue;
   seed_count++;
   int fail=-1;
   for(int idx:order)if((cs[idx].used[a*2]||cs[idx].used[a*2+1]||cs[idx].used[b*2]||cs[idx].used[b*2+1])&&!execute(T,cs[idx],dispatcher,dispatcher,20000)){fail=idx;break;}
   if(fail<0){std::cerr<<"Unrepaired survivor!\n";return 2;}
   std::bitset<512>footprint;execute(T,cs[fail],dispatcher,dispatcher,6000,false,&footprint);
   seed_out<<a<<" "<<b<<" "<<mask<<" "<<fail<<" "<<footprint.count()<<"\n";seed_out.flush();
   // If one changed row repairs this failing run within 6000 steps, the row
   // must appear before its first divergence, hence in this footprint.
   for(int q:states)if(q!=b)for(int bit:{0,1})if(footprint[q*2+bit]){
    Table U=T;
    for(int target:states)if(target!=b)for(int write:{0,1})for(int dir:{-1,1}){
     U[q][bit]={write,dir,target};repaired++;
     if(!execute(U,cs[fail],dispatcher,dispatcher,6000))continue;
     first_pass++;bool passes=true;
     for(int idx:quick)if(!execute(U,cs[idx],dispatcher,dispatcher,6000)){passes=false;break;}
     if(!passes)continue;
     // Check examples exercising the compensation too, including cases that
     // do not visit either merged state under the baseline.
     for(int idx:probes[q*2+bit])if(!execute(U,cs[idx],dispatcher,dispatcher,6000)){passes=false;break;}
     if(!passes)continue;quick_pass++;
     for(int idx:order)if(!execute(U,cs[idx],dispatcher,dispatcher,20000)){passes=false;break;}
     if(passes){success++;out<<a<<" "<<b<<" "<<mask<<" "<<q<<" "<<bit<<" "<<write<<" "<<dir<<" "<<target<<"\n";out.flush();std::cerr<<"SURVIVOR "<<a<<" "<<b<<" repair "<<q<<"/"<<bit<<"\n";}
    }
   }
   std::cerr<<"SEED "<<seed_count<<" merged "<<a<<" "<<b<<" "<<mask<<" trials "<<repaired<<" first "<<first_pass<<" quick "<<quick_pass<<" success "<<success<<"\n";
  }
 }
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 std::cerr<<"FINISH merge_seeds "<<seed_count<<" compensations "<<repaired<<" first_pass "<<first_pass<<" quick_pass "<<quick_pass<<" survivors "<<success<<" seconds "<<seconds<<"\n";
 std::ofstream summary("repair_summary.json");summary<<"{\"merged_seed_trials\":"<<merged<<",\"selected_seeds\":"<<seed_count<<",\"repair_trials\":"<<repaired<<",\"first_case_passes\":"<<first_pass<<",\"quick_passes\":"<<quick_pass<<",\"full_survivors\":"<<success<<",\"cases\":"<<nc<<",\"repair_fuel\":6000,\"final_fuel\":20000,\"seconds\":"<<seconds<<",\"finite_only\":true}\n";
}
