// Research diagnostics, 18 October 2026. See README.md for exact finite scopes.
// Bitset replay derived from attributed ProveIt resource_merge_search.cpp.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using Tape=std::array<uint64_t,4>;
struct Row {int w,d,t;};
using Table=std::array<std::array<Row,2>,256>;
struct Case {bool inc;int start,head,end;Tape initial{},target{};};
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
Table table,original;std::array<bool,6>assigned;std::vector<Case>cases;
long long nodes=0,programs=0,branches=0;int fuel=120;bool symmetry=true;std::ofstream out;auto began=std::chrono::steady_clock::now();
int rowid(int q,int b){return q==75?b:q==112?2+b:q==131?4+b:-1;}
bool endpoint(const Tape&t,const Case&c){
 if(t==c.target)return true;
 if(!c.inc)return false;
 // The final spare block may have any value from0 through4.
 for(int length=1;length<=5;length++){
  Tape target=c.target;set(target,c.end,0);set(target,c.end-1,0);
  for(int j=0;j<length;j++)set(target,c.end-1+j,1);
  if(t==target)return true;
 }
 return false;
}
int check(){
 for(auto&c:cases){
  int q=75,h=c.start;Tape tape=c.initial;bool done=false;
  for(int step=0;step<fuel;step++){
   if(q==7){if(h!=c.head||!endpoint(tape,c))return -1;done=true;break;}
   if(q==255||h<0||h>=256)return -1;
   int b=get(tape,h),id=rowid(q,b);if(id>=0&&!assigned[id])return id;
   Row r=table[q][b];set(tape,h,r.w);h+=r.d;q=r.t;
  }
  if(!done)return -1;
 }
 return 6;
}
void visit(int depth){
 nodes++;
 if(nodes%1000000==0){double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();std::cerr<<"NODES "<<nodes<<" leaves "<<programs<<" seconds "<<seconds<<"\n";}
 int needed=check();if(needed<0)return;
 if(needed==6){
  programs++;out<<"program "<<programs<<"\n";
  for(int q:{75,112,131})for(int b:{0,1}){auto r=table[q][b];out<<q<<" "<<b<<" "<<r.w<<" "<<r.d<<" "<<r.t<<"\n";}
  out.flush();std::cerr<<"FOUND "<<programs<<"\n";return;
 }
 int q=needed<2?75:needed<4?112:131,b=needed%2;
 assigned[needed]=true;
 for(int t:{75,112,131,48,63,7,2,4,20,95,109,73,83,42,14,10,6})for(int w:{0,1})for(int d:{-1,1}){
  // State112 and131 are internally named; break the interchangeable-name symmetry.
  if(symmetry&&depth==0&&t==131)continue;
  table[q][b]={w,d,t};branches++;visit(depth+1);
 }
 assigned[needed]=false;table[q][b]=original[q][b];
}
int main(int argc,char**argv){
 std::ifstream in(argv[1]);int nr;in>>nr;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;table[q][b]=r;}
 original=table;int nc;in>>nc;cases.resize(nc);
 for(auto&c:cases){int n,x;in>>c.inc>>c.start>>c.head>>n;for(int i=0;i<n;i++){in>>x;set(c.initial,x,1);}in>>n;for(int i=0;i<n;i++){in>>x;set(c.target,x,1);c.end=x;}}
 out.open(argv[2]);
 // Optional mode pins existing positive return and reverse unary scan.
 if(argc>3&&std::string(argv[3])=="fixed"){assigned[1]=true;assigned[3]=true;symmetry=false;}
 visit(0);double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 std::cerr<<"FINISH nodes "<<nodes<<" branches "<<branches<<" survivors "<<programs<<" seconds "<<seconds<<"\n";
}
