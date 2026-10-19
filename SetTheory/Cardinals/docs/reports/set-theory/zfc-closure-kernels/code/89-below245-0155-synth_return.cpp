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
struct Case{bool halt;int head;Tape initial{},target{};std::bitset<512> used;int steps;};
bool get(const Tape&t,int h){return(t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
Table table,original;std::array<bool,7>assigned;std::vector<Case>cases;std::vector<int>order;
long long nodes=0,programs=0,branches=0;int fuel=4000;std::ofstream out;auto began=std::chrono::steady_clock::now();
int rowid(int q,int b){return q==48?b:q==112?2+b:q==131?4+b:(q==75&&b==1)?6:-1;}
int execute(Case&c,bool record=false){
 Tape tape=c.initial;int h=64,q=96;
 for(int step=1;step<=fuel;step++){
  if(h<0||h>=2048||q==63)return -1;
  int b=get(tape,h),id=rowid(q,b);if(record)c.used.set(2*q+b);else if(id>=0&&!assigned[id])return id;
  auto r=table[q][b];set(tape,h,r.w);h+=r.d;q=r.t;
  if(q==254){if(record)c.steps=step;return c.halt?7:-1;}
  if(!c.halt&&q==96&&h==c.head+64&&tape==c.target){if(record)c.steps=step;return 7;}
 }
 return -1;
}
int check(){for(int i:order){int r=execute(cases[i]);if(r!=7)return r;}return 7;}
void visit(int depth){
 nodes++;
 if(nodes%100000==0){double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();std::cerr<<"NODES "<<nodes<<" leaves "<<programs<<" seconds "<<seconds<<"\n";}
 int needed=check();if(needed<0)return;
 if(needed==7){programs++;out<<"program "<<programs<<"\n";for(int q:{48,112,131})for(int b:{0,1}){auto r=table[q][b];out<<q<<" "<<b<<" "<<r.w<<" "<<r.d<<" "<<r.t<<"\n";}auto rr=table[75][1];out<<75<<" "<<1<<" "<<rr.w<<" "<<rr.d<<" "<<rr.t<<"\n";out.flush();std::cerr<<"FOUND "<<programs<<"\n";return;}
 int q=needed==6?75:needed<2?48:needed<4?112:131,b=needed==6?1:needed%2;assigned[needed]=true;
 for(int t:{48,112,131,7})for(int w:{0,1})for(int d:{-1}){
  if(needed==6&&(w!=1||t==7))continue;table[q][b]={w,d,t};branches++;visit(depth+1);
 }
 assigned[needed]=false;table[q][b]=original[q][b];
}
int main(int argc,char**argv){
 std::ifstream in(argv[1]);int nr;in>>nr;for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;table[q][b]=r;}
 original=table;int nc;in>>nc;cases.resize(nc);
 for(auto&c:cases){int n,x;in>>c.halt>>c.head>>n;for(int i=0;i<n;i++){in>>x;set(c.initial,x+64,1);}in>>n;for(int i=0;i<n;i++){in>>x;set(c.target,x+64,1);}}
 // Baseline collection temporarily permits state255.
 for(int i=0;i<nc;i++){
  auto&c=cases[i];Tape tape=c.initial;int q=96,h=64;bool good=false;
  for(int step=1;step<=20000;step++){int b=get(tape,h);c.used.set(2*q+b);auto r=table[q][b];set(tape,h,r.w);h+=r.d;q=r.t;if(q==254){good=c.halt;c.steps=step;break;}if(!c.halt&&q==96&&h==c.head+64&&tape==c.target){good=true;c.steps=step;break;}}
  if(!good){std::cerr<<"BASELINE FAIL\n";return 1;}
 }
 // Order two witnesses for each changing row and each old255 branch first.
 for(int key:{75*2+1,48*2,48*2+1,112*2,112*2+1,131*2,131*2+1}){
  int picked=0;for(int i=0;i<nc;i++)if(cases[i].used[key]){if(std::find(order.begin(),order.end(),i)==order.end())order.push_back(i);if(++picked>=2)break;}
 }
 std::vector<int>rest;for(int i=0;i<nc;i++)if(std::find(order.begin(),order.end(),i)==order.end())rest.push_back(i);
 std::mt19937 rng(844);std::shuffle(rest.begin(),rest.end(),rng);order.insert(order.end(),rest.begin(),rest.end());
 out.open(argv[2]);std::cerr<<"BASELINE "<<nc<<"\n";visit(0);double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();std::cerr<<"FINISH nodes "<<nodes<<" branches "<<branches<<" survivors "<<programs<<" seconds "<<seconds<<"\n";
}
