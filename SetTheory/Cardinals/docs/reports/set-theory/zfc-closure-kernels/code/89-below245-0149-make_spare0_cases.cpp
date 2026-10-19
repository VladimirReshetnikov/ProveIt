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

 old[255][0].w=0;
 int increments=0;
 for(auto&c:cs)if(c.used[255*2]){
  int last=2047;while(last>=0&&!get(c.target,last))last--;
  if(last<1||!get(c.target,last-1)||get(c.target,last-2)){std::cerr<<"Bad final B(1)\n";return 1;}
  set(c.target,last,0);increments++;
 }
 for(auto&c:cs)if(!execute(old,c,20000)){std::cerr<<"VARIANT FAILED\n";return 1;}
 std::ofstream out(argv[2]);out<<nr<<"\n";
 for(int q:states)for(int b:{0,1}){auto r=old[q][b];out<<q<<" "<<b<<" "<<r.w<<" "<<r.d<<" "<<r.t<<"\n";}
 out<<nc<<"\n";
 for(auto&c:cs){
  std::vector<int>a,b;for(int h=0;h<2048;h++){if(get(c.initial,h))a.push_back(h-64);if(get(c.target,h))b.push_back(h-64);}
  out<<c.halt<<" "<<c.head<<" "<<a.size();for(int x:a)out<<" "<<x;out<<" "<<b.size();for(int x:b)out<<" "<<x;out<<"\n";
 }
 std::cerr<<"PASS variant "<<nc<<" cases; increments "<<increments<<"\n";
}
