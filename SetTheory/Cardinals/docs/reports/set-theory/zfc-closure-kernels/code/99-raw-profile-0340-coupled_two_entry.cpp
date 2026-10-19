#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <vector>
// Simultaneous two-entry state deletion. Both incoming actions vary together;
// no individual-action pass is required. Fixed finite fixtures, no proof claim.
using Tape=std::array<uint64_t,32>;
struct Row {int w,d,t;};
using Table=std::array<Row,512>;
struct Case {bool halt;int head;Tape initial{},target{};std::bitset<512> used;int steps;};
struct Conf {Tape tape;int h=64,q=96,steps=0;};
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void put(Tape&t,int h,bool b){auto bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
// 0 rejects, 1 accepts, 2 suspends immediately before the chosen row.
int execute(const Table&T,Case&c,Conf&v,int pause=-1,bool record=false){
 for(;v.steps<20000;){
  if(v.h<0||v.h>=2048)return 0;
  int bit=get(v.tape,v.h), edge=v.q*2+bit;
  if(edge==pause)return 2;
  if(record)c.used.set(edge);
  auto r=T[edge];put(v.tape,v.h,r.w);v.h+=r.d;v.q=r.t;v.steps++;
  if(v.q==254){if(record)c.steps=v.steps;return c.halt?1:0;}
  if(!c.halt&&v.q==96&&v.h==c.head+64&&v.tape==c.target){if(record)c.steps=v.steps;return 1;}
 }
 return 0;
}
bool run(const Table&T,Case&c){Conf v{c.initial};return execute(T,c,v)==1;}
int main(int argc,char**argv){
 if(argc<3){std::cerr<<"usage: binary cases.txt output_prefix [deleted_state ...]\n";return 2;}
 std::ifstream in(argv[1]);Table base{};std::vector<int>states;int nr;in>>nr;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;base[2*q+b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case> cs(nc);
 for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;put(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;put(c.target,x+64,1);}}
 std::array<std::vector<int>,256>incoming;
 for(int q:states)for(int b:{0,1})if(base[2*q+b].t!=q)incoming[base[2*q+b].t].push_back(2*q+b);
 int maxsteps=0;std::bitset<512>used;
 for(auto&c:cs){Conf v{c.initial};if(execute(base,c,v,-1,true)!=1){std::cerr<<"BASELINE FAIL\n";return 1;}used|=c.used;maxsteps=std::max(maxsteps,c.steps);}
 std::cerr<<"BASELINE cases="<<nc<<" rows="<<used.count()<<" max="<<maxsteps<<"\n";
 std::vector<int>selected;
 if(argc>3)for(int a=3;a<argc;a++)selected.push_back(std::stoi(argv[a]));
 else for(int q:states)if(q!=95&&q!=96&&incoming[q].size()==2)selected.push_back(q);
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;
 std::mt19937 gen(20261018);std::shuffle(order.begin(),order.end(),gen);
 auto begun=std::chrono::steady_clock::now();
 std::ofstream out(std::string(argv[2])+".jsonl"),surv(std::string(argv[2])+"-survivors.txt");
 for(int gone:selected){
  if(incoming[gone].size()!=2){std::cerr<<"SKIP state "<<gone<<" degree "<<incoming[gone].size()<<"\n";continue;}
  int a=incoming[gone][0],b=incoming[gone][1];
  std::vector<int>affected,quick;
  for(int i:order)if(cs[i].used[a]||cs[i].used[b])affected.push_back(i);
  // Short independent witnesses often reject whole branches early.
  std::sort(affected.begin(),affected.end(),[&](int x,int y){return cs[x].steps<cs[y].steps;});
  int first=affected[0];
  // Orient the first edited edge before the suspended second edge. Prefer
  // a short witness using just one edge, when one exists.
  for(int i:affected)if(cs[i].used[a]!=cs[i].used[b]){first=i;break;}
  if(!cs[first].used[a])std::swap(a,b);
  else if(cs[first].used[b]){
   Conf v{cs[first].initial};
   for(int stp=0;stp<20000;stp++){
    int edge=v.q*2+get(v.tape,v.h);
    if(edge==a||edge==b){if(edge==b)std::swap(a,b);break;}
    auto r=base[edge];put(v.tape,v.h,r.w);v.h+=r.d;v.q=r.t;
   }
  }
  quick.push_back(first);
  for(int edge:{a,b}){int n=0;for(int i:affected)if(cs[i].used[edge]){if(std::find(quick.begin(),quick.end(),i)==quick.end())quick.push_back(i);if(++n==4)break;}}
  std::vector<Row>actions;for(int t:states)if(t!=gone)for(int w:{0,1})for(int d:{-1,1})actions.push_back({w,d,t});
  uint64_t branches=0,pairs=0,suspended=0,past=0,success=0;
  auto st=std::chrono::steady_clock::now();
  for(auto ra:actions){
   Table T=base;T[a]=ra;Conf prefix{cs[first].initial};
   int status=execute(T,cs[first],prefix,b);
   branches++;
   if(status==0)continue;
   if(status==2)suspended++;
   for(auto rb:actions){
    pairs++;T[b]=rb;
    if(status==2){Conf v=prefix;if(execute(T,cs[first],v)!=1)continue;}
    bool ok=true;
    for(int i:quick)if(i!=first&&!run(T,cs[i])){ok=false;break;}
    if(!ok)continue;past++;
    for(int i:affected)if(std::find(quick.begin(),quick.end(),i)==quick.end()&&!run(T,cs[i])){ok=false;break;}
    if(ok){success++;surv<<gone<<" "<<a/2<<" "<<a%2<<" "<<ra.w<<" "<<ra.d<<" "<<ra.t<<" "<<b/2<<" "<<b%2<<" "<<rb.w<<" "<<rb.d<<" "<<rb.t<<"\n";surv.flush();std::cerr<<"SURVIVOR gone="<<gone<<"\n";}
   }
  }
  double secs=std::chrono::duration<double>(std::chrono::steady_clock::now()-st).count();
  uint64_t family=actions.size()*actions.size();
  out<<"{\"deleted_state\":"<<gone<<",\"entry_rows\":[["<<a/2<<","<<a%2<<"],["<<b/2<<","<<b%2<<"]],\"family_size\":"<<family<<",\"first_actions\":"<<branches<<",\"first_actions_reaching_second_entry\":"<<suspended<<",\"joint_pairs_executed\":"<<pairs<<",\"past_quick\":"<<past<<",\"survivors\":"<<success<<",\"affected_cases\":"<<affected.size()<<",\"seconds\":"<<secs<<",\"finite_only\":true}\n";out.flush();
  std::cerr<<"STATE "<<gone<<" family="<<family<<" joint="<<pairs<<" past="<<past<<" survived="<<success<<" secs="<<secs<<"\n";
 }
 std::cerr<<"TOTAL seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begun).count()<<"\n";
}
