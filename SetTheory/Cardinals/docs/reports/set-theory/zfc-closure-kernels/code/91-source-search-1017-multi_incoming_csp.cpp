// Exhaust retained multi-entry products, learning exact nogoods from the changed rows visited by a failed literal execution.
// Simulator representation adapted from attributed zfc245-proof package's
// check_literal_cases.cpp, itself derived from ProveIt beyond246 merge_search.cpp.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
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
 std::ofstream out("multi-incoming-csp-survivors.txt"),summary("multi-incoming-csp-summary.json");
 summary<<"{\"local_ledger_entries\":"<<entries<<",\"products\":[";bool comma=false;
 for(int deleted:states){
  if(deleted==95||deleted==96||incoming[deleted].size()<3)continue;
  size_t n=passing[deleted].size();if(n>=64){std::cerr<<"TOO MANY ENTRIES\n";return 1;}
  uint64_t product=1;for(const auto& rows:passing[deleted])product*=rows.size();if(!product)continue;
  std::array<int,512>tracked;tracked.fill(-1);for(size_t j=0;j<n;j++){auto[p,b]=incoming[deleted][j];tracked[p*2+b]=j;}
  struct Nogood{uint64_t mask;std::vector<size_t> value;};
  std::vector<Nogood> forbidden;std::vector<size_t> choice(n,0);Table candidate=old;
  std::vector<uint64_t> domains(n);for(size_t j=0;j<n;j++){if(passing[deleted][j].size()>=64)return 1;domains[j]=(uint64_t(1)<<passing[deleted][j].size())-1;}
  bool done=false;uint64_t checked=0,covered=0;
  std::function<bool(std::vector<uint64_t>)> solve=[&](std::vector<uint64_t> dom){
   bool altered=true;
   while(altered){
    altered=false;
    for(const auto& clause:forbidden){
     bool irrelevant=false;size_t unresolved=0,last=0;
     for(size_t j=0;j<n;j++)if(clause.mask&(uint64_t(1)<<j)){
      uint64_t bit=uint64_t(1)<<clause.value[j];
      if(!(dom[j]&bit)){irrelevant=true;break;}
      if(dom[j]!=bit){unresolved++;last=j;}
     }
     if(irrelevant)continue;
     if(!unresolved)return false;
     if(unresolved==1){dom[last]&=~(uint64_t(1)<<clause.value[last]);if(!dom[last])return false;altered=true;}
    }
   }
   int selected=-1;uint64_t best=0;
   for(size_t j=0;j<n;j++)if(dom[j]&(dom[j]-1)){
    uint64_t score=1;for(const auto& clause:forbidden)if(clause.mask&(uint64_t(1)<<j))score+=1024/__builtin_popcountll(clause.mask);
    score=score*64/__builtin_popcountll(dom[j]);
    if(selected<0||score>best){selected=j;best=score;}
   }
   if(selected<0){for(size_t j=0;j<n;j++)choice[j]=__builtin_ctzll(dom[j]);return true;}
   for(uint64_t remaining=dom[selected];remaining;remaining&=remaining-1){uint64_t bit=remaining&-remaining;auto branch=dom;branch[selected]=bit;if(solve(branch))return true;}
   return false;
  };
  while(true){
   if(std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()>180){covered=checked;complete=false;break;}
   if(!solve(domains)){done=true;covered=product;break;}
   for(size_t j=0;j<n;j++){auto[p,b]=incoming[deleted][j];candidate[p][b]=passing[deleted][j][choice[j]];}
   checked++;bool good=true;uint64_t observed=0;
   for(int index:order){observed=0;if(!execute(candidate,cs[index],deleted,20000,false,&tracked,&observed)){good=false;break;}}
   if(good){success++;out<<deleted;for(size_t j=0;j<n;j++){auto[p,b]=incoming[deleted][j];Row r=passing[deleted][j][choice[j]];out<<" "<<p<<" "<<b<<" "<<r.w<<" "<<r.d<<" "<<r.t;}out<<"\n";out.flush();std::cerr<<"SURVIVOR "<<deleted<<"\n";observed=(uint64_t(1)<<n)-1;}
   else if(!observed){std::cerr<<"FAILURE WITH NO CHANGED ROW\n";return 1;}
   forbidden.push_back({observed,choice});
  }
  total_product+=product;total_checked+=checked;total_covered+=covered;
  if(comma)summary<<",";comma=true;
  summary<<"{\"deleted\":"<<deleted<<",\"product_size\":"<<product<<",\"literal_assignments_executed\":"<<checked<<",\"assignments_covered_lower_bound\":"<<covered<<",\"complete\":"<<(done?"true":"false")<<"}";
  std::cerr<<"deleted "<<deleted<<" product "<<product<<" executed "<<checked<<" covered "<<covered<<" complete "<<done<<"\n";
  if(!complete)break;
 }
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 summary<<"],\"complete_retained_products\":"<<(complete?"true":"false")<<",\"total_product_size\":"<<total_product<<",\"literal_assignments_executed\":"<<total_checked<<",\"assignments_covered_lower_bound\":"<<total_covered<<",\"full_literal_survivors\":"<<success<<",\"seconds\":"<<sec<<",\"instruction_cases\":"<<nc<<",\"fuel_per_case\":20000,\"tape_min\":-64,\"tape_max\":1983,\"finite_only\":true,\"separable_local_replacements_only\":true,\"pruning\":\"A nogood fixes exactly the replacement rows read during one failed execution; arbitrary choices of unread replacement rows preserve that same finite failure. Finite-domain unit propagation and exhaustive branching solve the retained product.\"}\n";
 std::cout<<"complete "<<complete<<" products "<<total_product<<" covered "<<total_covered<<" executed "<<total_checked<<" survivors "<<success<<" seconds "<<sec<<"\n";
}
