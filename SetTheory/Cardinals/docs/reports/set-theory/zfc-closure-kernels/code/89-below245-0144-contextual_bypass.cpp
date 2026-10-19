// Research diagnostics, 18 October 2026. See README.md for exact finite scopes.
// Bitset replay derived from attributed ProveIt resource_merge_search.cpp.
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
struct Row{int w,d,t;};
using Table=std::array<std::array<Row,2>,256>;
struct Case { bool halt;int head;Tape initial{},target{};std::bitset<512> used;int steps; };
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
bool execute(const Table&T,Case&c,int fuel,bool record=false){
 Tape tape=c.initial;int h=64,q=96;
 for(int step=1;step<=fuel;step++){
  if(h<0||h>=2048)return false;
  int b=get(tape,h);if(record)c.used.set(q*2+b);
  auto row=T[q][b];set(tape,h,row.w);h+=row.d;q=row.t;
  if(q==254){if(record)c.steps=step;return c.halt;}
  if(!c.halt&&q==96&&h==c.head+64&&tape==c.target){if(record)c.steps=step;return true;}
 }
 return false;
}
int main(int argc,char**argv){
 std::ifstream in(argv[1]);int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cs(nc);
 for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
 int maximum=0;for(auto&c:cs){if(!execute(old,c,20000,true)){std::cerr<<"BASE FAIL\n";return 1;}maximum=std::max(maximum,c.steps);}
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;std::mt19937 rng(90210);std::shuffle(order.begin(),order.end(),rng);
 std::array<std::vector<int>,256>probes;
 for(int q:states)for(int b:{0,1}){int found=0;for(int idx:order)if(cs[idx].used[2*q+b]){if(std::find(probes[q].begin(),probes[q].end(),idx)==probes[q].end())probes[q].push_back(idx);if(++found>=8)break;}}
 std::cerr<<"Baseline "<<nc<<" cases maximum "<<maximum<<"\n";

 long tested=0,full=0,success=0;auto begin=std::chrono::steady_clock::now();std::ofstream out(argv[2]);
 for(int erased:states){
  if(erased==95||erased==96)continue;
  std::vector<std::pair<int,int>> incoming;
  for(int q:states)if(q!=erased)for(int b:{0,1})if(old[q][b].t==erased)incoming.emplace_back(q,b);
  if(incoming.size()<2||incoming.size()>6)continue;
  std::vector<std::vector<Row>> alternatives;bool eligible=true;
  for(auto [caller,bit]:incoming){
   std::vector<int>affected,quick;
   for(int idx:order)if(cs[idx].used[2*caller+bit])affected.push_back(idx);
   for(int i=0;i<std::min(16,(int)affected.size());i++)quick.push_back(affected[i]);
   std::vector<Row> rows;
   for(int target:states)if(target!=erased)for(int write:{0,1})for(int move:{-1,1}){
    Table t=old;t[caller][bit]={write,move,target};bool good=true;tested++;
    for(int idx:quick)if(!execute(t,cs[idx],6000)){good=false;break;}
    if(!good)continue;full++;
    for(int idx:affected)if(!execute(t,cs[idx],10000)){good=false;break;}
    if(good)rows.push_back({write,move,target});
   }
   std::cerr<<"EDGE "<<caller<<"/"<<bit<<" into "<<erased<<" alternatives "<<rows.size()<<"\n";
   if(rows.empty()){eligible=false;break;}
   alternatives.push_back(rows);
  }
  if(!eligible)continue;
  int variants=1;for(auto &r:alternatives)variants*=r.size();
  std::cerr<<"COMPOSE "<<erased<<" variants "<<variants<<"\n";
  for(int number=0;number<variants;number++){
   int code=number;Table t=old;
   for(size_t i=0;i<incoming.size();i++){auto [q,b]=incoming[i];auto &rs=alternatives[i];t[q][b]=rs[code%rs.size()];code/=rs.size();}
   bool good=true;for(int idx:order)if(cs[idx].used[2*erased]||cs[idx].used[2*erased+1])if(!execute(t,cs[idx],10000)){good=false;break;}
   if(!good)continue;success++;out<<erased;
   for(auto [q,b]:incoming){auto r=t[q][b];out<<" | "<<q<<" "<<b<<" "<<r.w<<" "<<r.d<<" "<<r.t;}
   out<<"\n";out.flush();std::cerr<<"SURVIVOR erased "<<erased<<" variant "<<number<<"\n";
  }
 }
 auto seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();std::cerr<<"FINISH tested "<<tested<<" full "<<full<<" survived "<<success<<" seconds "<<seconds<<"\n";
}
