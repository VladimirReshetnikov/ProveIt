// Contextual merge discovery. This is finite evidence only.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>
using Tape=std::array<uint64_t,32>;
struct Row {int w,d,t;};
using Table=std::array<std::array<Row,2>,256>;
struct Case {bool halt; int head; Tape initial{},target{}; std::bitset<512> used;};
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
constexpr int R=9,K=18;
struct Snap {int q,h; uint32_t word;};
struct Context {int q; uint32_t word; std::vector<Snap> baseline;};
int mapped(int q,int a,int b){return q==b?a:q;}
std::array<std::set<uint32_t>,512> windows;
std::array<std::vector<Context>,512> contexts;
bool execute(const Table&T,Case&c,int start,int finish,int fuel,bool record=false){
 Tape tape=c.initial;int h=64,q=start;
 for(int step=1;step<=fuel;step++){
  if(h<0||h>=2048)return false;
  int b=get(tape,h);
  if(record){c.used.set(q*2+b);if(h>=R&&h<2048-R){uint32_t w=0;for(int j=-R;j<=R;j++)w|=uint32_t(get(tape,h+j))<<(j+R);windows[q*2+b].insert(w);}}
  Row row=T[q][b];set(tape,h,row.w);h+=row.d;q=row.t;
  if(q==254)return c.halt;
  if(!c.halt&&q==finish&&h==c.head+64&&tape==c.target)return true;
 }
 return false;
}
bool matches(int q,int h,uint32_t word,const std::vector<Snap>&refs,int a,int b){for(auto&r:refs)if(q==mapped(r.q,a,b)&&h==r.h&&word==r.word)return true;return false;}
bool compatible(const Table&old,int a,int b,Row choice,const Context&ctx){
 int q=a,h=R;uint32_t word=ctx.word;
 for(int k=0;k<K;k++){
  int bit=(word>>h)&1;
  Row row=k==0?choice:old[q][bit];
  if(row.w)word|=uint32_t(1)<<h;else word&=~(uint32_t(1)<<h);
  h+=row.d;q=mapped(row.t,a,b);
  if(matches(q,h,word,ctx.baseline,a,b))return true;
  if(q==a||q==254||h<0||h>2*R)return false;
 }
 return false;
}
int main(int argc,char**argv){
 std::ifstream in(argc>1?argv[1]:"current245-cases.txt");int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cs(nc);
 for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
 for(auto&c:cs)if(!execute(old,c,96,96,10000,true)){std::cerr<<"BASELINE FAIL\n";return 1;}
 long ncontext=0;
 for(int q:states)for(int bit=0;bit<2;bit++){
  std::vector<uint32_t>ws(windows[q*2+bit].begin(),windows[q*2+bit].end());
  std::mt19937 rng(9517+q*2+bit);std::shuffle(ws.begin(),ws.end(),rng);
  // Full observed context set; shuffled for rapid rejection.
  for(uint32_t w:ws){Context ctx{q,w,{}};int qq=q,h=R;uint32_t word=w;
   for(int k=0;k<K;k++){int bb=(word>>h)&1;Row r=old[qq][bb];if(r.w)word|=uint32_t(1)<<h;else word&=~(uint32_t(1)<<h);h+=r.d;qq=r.t;ctx.baseline.push_back({qq,h,word});if(qq==254||h<0||h>2*R)break;}
   contexts[q*2+bit].push_back(std::move(ctx));
  }
  ncontext+=ws.size();
 }
 std::cerr<<"CONTEXTS "<<ncontext<<"\n";
 std::ofstream out("local-merge-survivors.txt");long proposals=0,local=0,full=0;auto began=std::chrono::steady_clock::now();
 std::vector<int>targets=states;targets.push_back(254);
 for(size_t ai=0;ai<states.size();ai++)for(size_t bi=ai+1;bi<states.size();bi++){
  int a=states[ai],b=states[bi];std::array<std::vector<Row>,2>allowed;
  for(int bit=0;bit<2;bit++){
   for(int t:targets)if(t!=b)for(int w=0;w<2;w++)for(int d:{-1,1}){
    Row choice{w,d,t};proposals++;bool good=true;
    for(int q:{a,b}){for(auto&c:contexts[q*2+bit])if(!compatible(old,a,b,choice,c)){good=false;break;}if(!good)break;}
    if(good)allowed[bit].push_back(choice);
   }
   if(allowed[bit].empty())break;
  }
  if(allowed[0].empty()||allowed[1].empty())continue;
  for(Row r0:allowed[0])for(Row r1:allowed[1]){
   local++;Table T=old;T[a][0]=r0;T[a][1]=r1;
   for(int q:states)if(q!=b)for(int bb=0;bb<2;bb++)T[q][bb].t=mapped(T[q][bb].t,a,b);
   bool good=true;for(auto&c:cs)if((c.used[a*2]||c.used[a*2+1]||c.used[b*2]||c.used[b*2+1])&&!execute(T,c,mapped(96,a,b),mapped(96,a,b),20000)){good=false;break;}
   if(good){full++;out<<a<<' '<<b<<' '<<r0.w<<' '<<r0.d<<' '<<r0.t<<' '<<r1.w<<' '<<r1.d<<' '<<r1.t<<'\n';out.flush();std::cerr<<"SURVIVOR "<<a<<" "<<b<<"\n";}
  }
 }
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 std::cerr<<"FINISH proposals "<<proposals<<" local "<<local<<" full "<<full<<" seconds "<<sec<<"\n";
 std::ofstream summary("local-merge-summary.json");summary<<"{\"action_proposals\":"<<proposals<<",\"local_pairs\":"<<local<<",\"full_survivors\":"<<full<<",\"contexts\":"<<ncontext<<",\"radius\":"<<R<<",\"local_steps\":"<<K<<",\"finite_only\":true,\"seconds\":"<<sec<<"}\n";
}
