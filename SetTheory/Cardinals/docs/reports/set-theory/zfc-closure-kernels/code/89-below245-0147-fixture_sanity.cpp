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

 auto audit=[&](const std::string&name,const Table&t,bool expected){
  int passed=0,first=-1;for(int i=0;i<nc;i++){if(execute(t,cs[i],20000))passed++;else if(first<0)first=i;}
  if((passed==nc)!=expected){std::cerr<<"Unexpected sanity result "<<name<<"\n";std::exit(2);}
  std::cout<<"{\"name\":\""<<name<<"\",\"passed_cases\":"<<passed<<",\"total_cases\":"<<nc<<",\"first_failure\":"<<first<<",\"expected_all_pass\":"<<(expected?"true":"false")<<"}";
 };
 std::cout<<"{\"status\":\"PASS\",\"controls\":[";audit("original",old,true);
 Table renamed{};auto ren=[](int q){return q==131?255:q==255?131:q;};
 for(int q:states)for(int b:{0,1}){auto r=old[q][b];r.t=ren(r.t);renamed[ren(q)][b]=r;}
 std::cout<<",";audit("equivalent_state_permutation_131_255",renamed,true);
 Table premature=old;premature[75][0]={1,1,254};std::cout<<",";audit("premature_halt_75_read0",premature,false);
 Table trap=old;trap[77][1]={1,1,0};trap[0][0]={0,1,0};trap[0][1]={1,1,0};std::cout<<",";audit("replaced_halt_by_absorbing_loop",trap,false);
 std::cout<<"],\"fuel_per_case\":20000,\"scope\":\"Finite simulator mutation sanity; state renaming is exactly equivalent, and injected premature halt and absorbing loop are deliberate faults.\"}\n";
}
