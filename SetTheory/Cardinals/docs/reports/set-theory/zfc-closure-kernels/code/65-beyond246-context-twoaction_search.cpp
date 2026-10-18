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

using Tape=std::array<uint64_t,8>;
struct Row{int w,d,t;};using Table=std::array<std::array<Row,2>,256>;
struct Case{bool halt;int head;Tape initial{},target{};std::bitset<512>used;};
struct Spec{int dead;std::array<int,2>hole;};
enum class Result{PASS,FAIL,HOLE0,HOLE1};
bool get(const Tape&t,int h){return(t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}

Result execute(const Table&T,Case&c,int fuel,const Spec&s,const std::array<bool,2>&assigned,const std::array<Row,2>&actions,bool record=false){
 Tape tape=c.initial,anchor=c.initial;int h=64,q=96,ah=64,aq=96,power=1,span=0;
 for(int tick=0;tick<fuel;tick++){
  if(h<0||h>=512||q==s.dead)return Result::FAIL;
  int b=get(tape,h),key=q*2+b;Row row=T[q][b];
  if(record)c.used.set(key);
  if(key==s.hole[0]){if(!assigned[0])return Result::HOLE0;row=actions[0];}
  if(key==s.hole[1]){if(!assigned[1])return Result::HOLE1;row=actions[1];}
  set(tape,h,row.w);h+=row.d;q=row.t;
  if(q==254)return c.halt?Result::PASS:Result::FAIL;
  if(!c.halt&&q==96&&h==c.head+64&&tape==c.target)return Result::PASS;
  // Brent-style exact configuration repetition, with no probabilistic hashes.
  // With assigned actions fixed, repetition certifies a deterministic cycle.
  span++;
  if(q==aq&&h==ah&&tape==anchor)return Result::FAIL;
  if(span==power){anchor=tape;aq=q;ah=h;power*=2;span=0;}
 }
 return Result::FAIL;
}

int main(int argc,char**argv){
 std::ifstream in(argc>1?argv[1]:"merge-cases.txt");int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cases(nc);
 for(auto &c:cases){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
 Spec absent{-1,{-1,-1}};std::array<bool,2>yes={true,true};std::array<Row,2>dummy{};
 for(auto &c:cases)if(execute(old,c,20000,absent,yes,dummy,true)!=Result::PASS){std::cerr<<"BASELINE FAIL\n";return 1;}
 std::ifstream specfile(argc>2?argv[2]:"twoaction-states.txt");int ns;specfile>>ns;std::vector<Spec>specs(ns);
 for(auto&s:specs){int a,b,c,d;specfile>>s.dead>>a>>b>>c>>d;s.hole={2*a+b,2*c+d};}
 std::cerr<<"Baseline "<<nc<<" cases; "<<ns<<" eligible states\n";
 constexpr int PROBE_FUEL=2000;
 std::ofstream survivor("twoaction-survivors.txt"),summary("twoaction-search-summary.json");summary<<"{\"finite_only\":true,\"cases\":"<<nc<<",\"probe_fuel_per_case\":"<<PROBE_FUEL<<",\"full_survivor_fuel_per_case\":20000,\"states\":[";bool firststate=true;
 auto began=std::chrono::steady_clock::now();uint64_t totalnodes=0,totalchecks=0,totalmass=0,totalsurvivors=0;
 for(auto s:specs){
  std::vector<int>ids;for(int i=0;i<nc;i++)if(cases[i].used[s.hole[0]]||cases[i].used[s.hole[1]]||cases[i].used[2*s.dead]||cases[i].used[2*s.dead+1])ids.push_back(i);
  std::vector<Row>domain;for(int w:{0,1})for(int d:{-1,1}){for(int t:states)if(t!=s.dead)domain.push_back({w,d,t});domain.push_back({w,d,254});}
  std::array<bool,2>assigned={false,false};std::array<Row,2>actions{};
  uint64_t nodes=0,checks=0,mass=0,leaves=0;auto start=std::chrono::steady_clock::now();
  std::function<void()>visit=[&](){
   nodes++;
   for(size_t at=0;at<ids.size();at++){
    checks++;Result result=execute(old,cases[ids[at]],PROBE_FUEL,s,assigned,actions);
    if(result==Result::FAIL){
     int bad=ids[at];std::move_backward(ids.begin(),ids.begin()+at,ids.begin()+at+1);ids[0]=bad;
     uint64_t covered=1;for(bool flag:assigned)if(!flag)covered*=domain.size();mass+=covered;return;
    }
    if(result==Result::HOLE0||result==Result::HOLE1){
     int h=result==Result::HOLE0?0:1;
     assigned[h]=true;for(auto action:domain){actions[h]=action;visit();}assigned[h]=false;return;
    }
   }
   for(int h=0;h<2;h++)if(!assigned[h]){assigned[h]=true;for(auto action:domain){actions[h]=action;visit();}assigned[h]=false;return;}
   for(auto &c:cases)if(execute(old,c,20000,s,assigned,actions)!=Result::PASS){std::cerr<<"UNEXPECTED FULL CASE FAILURE\n";std::exit(2);}
   leaves++;survivor<<s.dead;for(int h=0;h<2;h++)survivor<<" "<<s.hole[h]/2<<" "<<s.hole[h]%2<<" "<<actions[h].w<<" "<<actions[h].d<<" "<<actions[h].t;survivor<<"\n";survivor.flush();
   std::cerr<<"SURVIVOR "<<s.dead;for(auto a:actions)std::cerr<<" "<<a.w<<" "<<a.d<<" "<<a.t;std::cerr<<"\n";
  };
  visit();uint64_t planned=uint64_t(domain.size())*domain.size();if(mass+leaves!=planned){std::cerr<<"PARTITION ERROR\n";return 3;}
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
  totalnodes+=nodes;totalchecks+=checks;totalmass+=mass;totalsurvivors+=leaves;
  std::cerr<<"STATE "<<s.dead<<" mass "<<mass<<" leaves "<<leaves<<" nodes "<<nodes<<" checks "<<checks<<" seconds "<<seconds<<"\n";
  if(!firststate)summary<<",";firststate=false;
  summary<<"{\"deleted\":"<<s.dead<<",\"planned\":"<<planned<<",\"pruned\":"<<mass<<",\"survivors\":"<<leaves<<",\"nodes\":"<<nodes<<",\"checks\":"<<checks<<",\"seconds\":"<<seconds<<"}";summary.flush();
 }
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 summary<<"],\"total_nodes\":"<<totalnodes<<",\"total_checks\":"<<totalchecks<<",\"pruned_mass\":"<<totalmass<<",\"survivors\":"<<totalsurvivors<<",\"seconds\":"<<seconds<<"}\n";
 std::cerr<<"FINISH mass "<<totalmass<<" survivors "<<totalsurvivors<<" seconds "<<seconds<<"\n";
}
