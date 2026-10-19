// Adapted from ProveIt incoming beyond246 merge_search.cpp. Original algorithm credited in NOTICE.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <numeric>
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
  std::ifstream in(argv[1]);int nr;in>>nr;Table old{};std::vector<int>states;
  for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
  int nc;in>>nc;std::vector<Case>cs(nc);
  for(auto &c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
  std::vector<int>order(nc);std::iota(order.begin(),order.end(),0);std::mt19937 rng(12461018);std::shuffle(order.begin(),order.end(),rng);
  int total=0,success=0;std::ofstream out("combined-reroute-survivors.txt");
  for(int erased:{4,42}){
    std::vector<std::pair<int,int>> keys;std::vector<std::vector<int>>opts;
    if(erased==4){keys={{2,1},{6,1},{9,1},{13,1},{19,1},{29,1},{41,1},{58,1}};opts={{6,9},{9},{6,9},{6,9},{6,9,13},{2,6,9,13},{2,6,9,13},{2,6,9,13}};}
    else{keys={{30,0},{57,0}};opts={{39,70,72,93,169,201},{21,25,49,53,173}};}
    std::vector<int>choice(keys.size());int tested=0,passed=0;
    auto dfs=[&](auto&&self,int i,Table T)->void{
      if(i==(int)keys.size()){
        tested++;total++;
        for(int index:order)if(!execute(T,cs[index],96,96,20000))return;
        passed++;success++;out<<erased;for(int v:choice)out<<" "<<v;out<<"\n";out.flush();return;
      }
      auto [q,b]=keys[i];for(int t:opts[i]){T[q][b].t=t;choice[i]=t;self(self,i+1,T);}
    };
    dfs(dfs,0,old);std::cout<<"ERASE "<<erased<<" recipes "<<tested<<" survivors "<<passed<<"\n";
  }
  std::ofstream summary("combined-reroute-summary.json");summary<<"{\"candidate_count\":"<<total<<",\"survivors\":"<<success<<",\"cases\":"<<nc<<",\"finite_only\":true}\n";
}
