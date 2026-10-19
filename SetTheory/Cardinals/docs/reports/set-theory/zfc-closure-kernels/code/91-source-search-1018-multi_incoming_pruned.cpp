// Exhaust retained multi-entry products, pruning only literal-failure-invariant suffixes.
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
bool execute(const Table&T,Case&c,int deleted,int fuel,bool record=false,const std::array<int,512>* tracked=nullptr,uint64_t* observed=nullptr){
 Tape tape=c.initial;int h=64,q=96;
 for(int step=1;step<=fuel;step++){
  if(h<0||h>=2048||q==deleted)return false;
  int b=get(tape,h);if(record)c.used.set(q*2+b);if(tracked&&(*tracked)[q*2+b]>=0)*observed|=uint64_t(1)<<(*tracked)[q*2+b];
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
 for(auto&c:cs)if(!execute(old,c,-1,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}
 std::array<std::vector<std::pair<int,int>>,256>incoming;
 for(int q:states)for(int b:{0,1})if(old[q][b].t!=q)incoming[old[q][b].t].push_back({q,b});
 std::array<std::vector<std::vector<Row>>,256> passing;
 for(int q:states)passing[q].resize(incoming[q].size());
 std::ifstream ledger(argv[2]);int q,e,p,b,w,d,t;size_t entries=0;
 while(ledger>>q>>e>>p>>b>>w>>d>>t){
  if(q<0||q>=256||e<0||e>=int(incoming[q].size())||incoming[q][e]!=std::pair<int,int>{p,b}||t==q){std::cerr<<"BAD LOCAL LEDGER\n";return 1;}
  passing[q][e].push_back({w,d,t});entries++;
 }
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;std::mt19937 rng(20261019);std::shuffle(order.begin(),order.end(),rng);
 auto began=std::chrono::steady_clock::now();uint64_t total_product=0,total_checked=0,total_covered=0,success=0;bool complete=true;
 std::ofstream out("multi-incoming-pruned-survivors.txt"),summary("multi-incoming-pruned-summary.json");
 summary<<"{\"local_ledger_entries\":"<<entries<<",\"products\":[";bool comma=false;
 for(int deleted:states){
  if(deleted==95||deleted==96||incoming[deleted].size()<3)continue;
  size_t n=passing[deleted].size();if(n>=64){std::cerr<<"TOO MANY ENTRIES\n";return 1;}
  uint64_t product=1;for(const auto& rows:passing[deleted])product*=rows.size();if(!product)continue;
  std::array<int,512>tracked;tracked.fill(-1);for(size_t j=0;j<n;j++){auto[p,b]=incoming[deleted][j];tracked[p*2+b]=j;}
  std::vector<size_t> choice(n,0);Table candidate=old;bool done=false;uint64_t checked=0,covered=0;
  auto rank=[&](){uint64_t r=0;for(size_t j=0;j<n;j++)r=r*passing[deleted][j].size()+choice[j];return r;};
  while(!done){
   if(checked%1000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()>180){complete=false;break;}
   for(size_t j=0;j<n;j++){auto[p,b]=incoming[deleted][j];candidate[p][b]=passing[deleted][j][choice[j]];}
   checked++;bool good=true;uint64_t observed=0;
   for(int index:order){observed=0;if(!execute(candidate,cs[index],deleted,20000,false,&tracked,&observed)){good=false;break;}}
   int pivot=n-1;
   if(good){success++;out<<deleted;for(size_t j=0;j<n;j++){auto[p,b]=incoming[deleted][j];Row r=passing[deleted][j][choice[j]];out<<" "<<p<<" "<<b<<" "<<r.w<<" "<<r.d<<" "<<r.t;}out<<"\n";out.flush();std::cerr<<"SURVIVOR "<<deleted<<"\n";}
   else{if(!observed){std::cerr<<"FAILURE WITH NO CHANGED ROW\n";return 1;}while(pivot>=0&&!(observed&(uint64_t(1)<<pivot)))pivot--;}
   for(size_t j=pivot+1;j<n;j++)choice[j]=0;
   while(pivot>=0){choice[pivot]++;if(choice[pivot]<passing[deleted][pivot].size())break;choice[pivot]=0;pivot--;}
   done=pivot<0;covered=done?product:rank();
  }
  total_product+=product;total_checked+=checked;total_covered+=covered;
  if(comma)summary<<",";comma=true;
  summary<<"{\"deleted\":"<<deleted<<",\"product_size\":"<<product<<",\"literal_assignments_executed\":"<<checked<<",\"assignments_covered\":"<<covered<<",\"complete\":"<<(done?"true":"false")<<"}";
  std::cerr<<"deleted "<<deleted<<" product "<<product<<" executed "<<checked<<" covered "<<covered<<" complete "<<done<<"\n";
  if(!complete)break;
 }
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 summary<<"],\"complete_retained_products\":"<<(complete?"true":"false")<<",\"total_product_size\":"<<total_product<<",\"literal_assignments_executed\":"<<total_checked<<",\"assignments_covered\":"<<total_covered<<",\"full_literal_survivors\":"<<success<<",\"seconds\":"<<sec<<",\"instruction_cases\":"<<nc<<",\"fuel_per_case\":20000,\"tape_min\":-64,\"tape_max\":1983,\"finite_only\":true,\"separable_local_replacements_only\":true,\"pruning\":\"At a failed execution, only choices strictly after its rightmost visited replacement row are varied in the skipped suffix. Those choices cannot change that finite trace.\"}\n";
 std::cout<<"complete "<<complete<<" products "<<total_product<<" covered "<<total_covered<<" executed "<<total_checked<<" survivors "<<success<<" seconds "<<sec<<"\n";
}
