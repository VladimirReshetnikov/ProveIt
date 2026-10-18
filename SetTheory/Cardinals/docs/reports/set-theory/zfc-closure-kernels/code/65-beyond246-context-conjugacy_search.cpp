#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>

using Tape=std::array<uint64_t,8>;
struct Row{int w,d,t;};using Table=std::array<std::array<Row,2>,256>;
struct Input{int kind,arg,positive,head,span;std::string pc,next;};
struct Case{bool halt;int head;Tape initial{},target{};};
struct Family{Input spec;std::array<Case,9>cases;};
bool get(const Tape&t,int h){return(t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
Tape paint(std::string pc,int head,int span,std::vector<int>regs){
 Tape t{};set(t,head-1+64,1);set(t,head+span+64,1);
 for(size_t i=0;i<pc.size();i++)if(pc[i]=='1')set(t,head+i+64,1);
 int pos=head+span+1;for(int v:regs){for(int j=1;j<v+2;j++)set(t,pos+j+64,1);pos+=v+2;}return t;
}
Case make(const Input&s,int physical){
 std::vector<int>regs;for(int i=0;i<9;i++)regs.push_back((i*3+1)%5);regs.push_back(0);regs.push_back(2);
 if(s.kind==1)regs[physical]=s.positive?2:0;
 Case c;c.halt=s.kind==4;c.head=s.head;c.initial=paint(s.pc,0,40,regs);
 if(s.kind==0){regs[physical]++;regs.push_back(1);}else if(s.kind==1&&s.positive)regs[physical]--;
 c.target=paint(s.next,s.head,s.span,regs);return c;
}
bool execute(const Table&T,const Case&c,int dispatcher,int fuel){
 Tape tape=c.initial;int h=64,q=dispatcher;
 for(int n=1;n<=fuel;n++){
  if(h<0||h>=512)return false;int b=get(tape,h);Row row=T[q][b];set(tape,h,row.w);h+=row.d;q=row.t;
  if(q==254)return c.halt;
  if(!c.halt&&q==dispatcher&&h==c.head+64&&tape==c.target)return true;
 }return false;
}
int infer(const Table&T,const Family&f,int dispatcher,int fuel){
 Tape tape=f.cases[0].initial;int h=64,q=dispatcher;
 for(int n=1;n<=fuel;n++){
  if(h<0||h>=512)return -1;int b=get(tape,h);Row row=T[q][b];set(tape,h,row.w);h+=row.d;q=row.t;
  if(q==254)return -1;
  if(q==dispatcher&&h==f.cases[0].head+64)for(int r=0;r<9;r++)if(tape==f.cases[r].target)return r;
 }return -1;
}
int main(int argc,char**argv){
 std::ifstream in(argc>1?argv[1]:"conjugacy-cases.txt");int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Family>families(nc);std::array<int,9>first;first.fill(-1);
 for(int i=0;i<nc;i++){auto &f=families[i];auto&s=f.spec;in>>s.kind>>s.arg>>s.positive>>s.pc>>s.next>>s.head>>s.span;if(s.next==".")s.next="";for(int r=0;r<9;r++)f.cases[r]=make(s,r);
  if(s.kind==0&&(first[s.arg]<0||s.pc.size()<families[first[s.arg]].spec.pc.size()))first[s.arg]=i;}
 std::array<int,9>original={6,2,0,4,3,7,8,5,1};
 for(const auto&f:families)if(!execute(old,f.cases[f.spec.kind<2?original[f.spec.arg]:0],96,20000)){std::cerr<<"BASELINE FAIL\n";return 1;}
 std::cerr<<"Baseline "<<nc<<" cases; CI representatives";for(int i:first)std::cerr<<" "<<i;std::cerr<<"\n";
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;std::mt19937 rng(20261018);std::shuffle(order.begin(),order.end(),rng);
 auto began=std::chrono::steady_clock::now();int tested=0,inferred=0,bijective=0,success=0;
 std::ofstream out("conjugacy-survivors.txt");
 for(size_t ai=0;ai<states.size();ai++)for(size_t bi=ai+1;bi<states.size();bi++){
  int a=states[ai],b=states[bi];
  for(int mask=0;mask<4;mask++){
   Table T=old;for(int bit=0;bit<2;bit++)T[a][bit]=old[(mask&(1<<bit))?b:a][bit];
   for(int q:states)if(q!=b)for(int bit=0;bit<2;bit++)if(T[q][bit].t==b)T[q][bit].t=a;
   int dispatcher=96==b?a:96;bool good=true;tested++;std::array<int,9>perm;
   for(int r=0;r<9;r++){perm[r]=infer(T,families[first[r]],dispatcher,20000);if(perm[r]<0){good=false;break;}}
   if(!good)continue;inferred++;
   auto sorted=perm;std::sort(sorted.begin(),sorted.end());if(sorted!=std::array<int,9>{0,1,2,3,4,5,6,7,8})continue;bijective++;
   for(int idx:order){const auto&f=families[idx];if(!execute(T,f.cases[f.spec.kind<2?perm[f.spec.arg]:0],dispatcher,20000)){good=false;break;}}
   if(good){success++;out<<a<<" "<<b<<" "<<mask;for(int r:perm)out<<" "<<r;out<<"\n";out.flush();std::cerr<<"SURVIVOR "<<a<<" "<<b<<" "<<mask<<"\n";}
  }
  if(tested%10000==0)std::cerr<<"done "<<tested<<" inferred "<<inferred<<" bijections "<<bijective<<" survivors "<<success<<"\n";
 }
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 std::cerr<<"FINISH candidates "<<tested<<" inferred "<<inferred<<" bijections "<<bijective<<" survivors "<<success<<" seconds "<<seconds<<"\n";
 std::ofstream summary("conjugacy-search-summary.json");summary<<"{\"candidate_count\":"<<tested<<",\"inferred_maps\":"<<inferred<<",\"inferred_bijections\":"<<bijective<<",\"full_literal_pass_count\":"<<success<<",\"instruction_cases\":"<<nc<<",\"fuel_per_case\":20000,\"seconds\":"<<seconds<<",\"finite_only\":true}\n";
}
