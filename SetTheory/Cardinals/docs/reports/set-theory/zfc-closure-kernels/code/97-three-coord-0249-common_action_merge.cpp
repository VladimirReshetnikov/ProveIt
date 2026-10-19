#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>

// Discovery only. A survivor must pass an independent universal verifier.
// The literal simulator and fixture format are adapted from ProveIt's
// routing245 code/state_reduction/resource_merge_search.cpp. Retained
// upstream attribution and licenses are supplied in licenses/.
using Tape=std::array<uint64_t,32>;
struct Row { int w,d,t; bool operator==(const Row&o)const{return w==o.w&&d==o.d&&t==o.t;} };
using Table=std::array<std::array<Row,2>,256>;
struct Case { bool halt; int head; Tape initial{},target{}; };
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void setbit(Tape&t,int h,bool b){uint64_t bit=uint64_t(1)<<(h&63);if(b)t[h>>6]|=bit;else t[h>>6]&=~bit;}
constexpr int CENTER=31,WIDTH=63,HORIZON=30;
uint64_t window(const Tape&t,int h){
  uint64_t v=0;for(int j=0;j<WIDTH;j++){int x=h+j-CENTER;if(x>=0&&x<2048&&get(t,x))v|=uint64_t(1)<<j;}return v;
}
struct Cfg {int q,h;uint64_t tape;bool operator==(const Cfg&o)const{return q==o.q&&h==o.h&&tape==o.tape;}};
bool step(const Table&T,Cfg&c){
  if(c.h<0||c.h>=WIDTH||c.q==254)return false;
  int b=(c.tape>>c.h)&1;auto r=T[c.q][b];uint64_t bit=uint64_t(1)<<c.h;
  if(r.w)c.tape|=bit;else c.tape&=~bit;c.h+=r.d;c.q=r.t;return true;
}
bool fits(const Table&T,int key,int eliminated,uint64_t tape,Row action){
  Cfg base{key/2,CENTER,tape};std::vector<Cfg> future;
  for(int i=0;i<HORIZON;i++){if(!step(T,base))break;if(base.q!=eliminated)future.push_back(base);}
  Cfg alt{action.t,CENTER+action.d,tape};uint64_t bit=uint64_t(1)<<CENTER;
  if(action.w)alt.tape|=bit;else alt.tape&=~bit;
  for(int j=0;j<HORIZON;j++){
    if(alt.q==eliminated)return false;
    if(std::find(future.begin(),future.end(),alt)!=future.end())return true;
    if(alt.q==254&&std::any_of(future.begin(),future.end(),[](const Cfg&c){return c.q==254;}))return true;
    if(!step(T,alt))return false;
  }
  return false;
}
bool execute(const Table&T,const Case&c){
  Tape tape=c.initial;int h=64,q=96;
  for(int step=1;step<=20000;step++){
    if(h<0||h>=2048)return false;int b=get(tape,h);auto row=T[q][b];setbit(tape,h,row.w);h+=row.d;q=row.t;
    if(q==254)return c.halt;
    if(!c.halt&&q==96&&h==c.head+64&&tape==c.target)return true;
  }return false;
}
int main(int argc,char**argv){
  if(argc!=2){std::cerr<<"Usage: common_action_merge cases.txt\n";return 2;}
  std::ifstream in(argv[1]);int nr;in>>nr;Table T{};std::vector<int>states;
  if(!in){std::cerr<<"Could not read the fixture input\n";return 2;}
  for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;T[q][b]=r;if(!b)states.push_back(q);}
  int nc;in>>nc;std::vector<Case>cs(nc);
  for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;setbit(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;setbit(c.target,x+64,1);}}
  std::array<std::unordered_set<uint64_t>,512> windows;
  std::array<std::vector<int>,256> incoming;
  for(int q:states)for(int b=0;b<2;b++)incoming[T[q][b].t].push_back(q*2+b);
  for(int ci=0;ci<nc;ci++){
    auto&c=cs[ci];Tape tape=c.initial;int h=64,q=96;bool ok=false;
    for(int step=1;step<=20000;step++){
      if(h<0||h>=2048)break;int b=get(tape,h);windows[q*2+b].insert(window(tape,h));
      auto r=T[q][b];setbit(tape,h,r.w);h+=r.d;q=r.t;
      if(q==254){ok=c.halt;break;}
      if(!c.halt&&q==96&&h==c.head+64&&tape==c.target){ok=true;break;}
    }
    if(!ok){std::cerr<<"Baseline failed "<<ci<<"\n";return 1;}
  }
  size_t nw=0;for(auto&w:windows)nw+=w.size();std::cerr<<"Collected "<<nw<<" windows from "<<nc<<" cases\n";

  std::array<std::vector<Row>,512> possible;
  std::ofstream actout("admissible-actions.txt");
  for(int q:states)for(int b=0;b<2;b++){
    int key=2*q+b;
    if(windows[key].empty())continue;
    std::vector<uint64_t>ws(windows[key].begin(),windows[key].end());
    std::mt19937 rng(key+20261018);std::shuffle(ws.begin(),ws.end(),rng);
    std::vector<int>targets=states;targets.push_back(254);
    for(int t:targets)for(int d:{-1,1})for(int w:{0,1}){
      Row r{w,d,t};bool good=true;
      for(uint64_t win:ws)if(!fits(T,key,-1,win,r)){good=false;break;}
      if(good){possible[key].push_back(r);actout<<q<<" "<<b<<" "<<w<<" "<<d<<" "<<t<<"\n";}
    }
    actout.flush();
  }
  int candidate_pairs=0, fulltests=0, survivors=0;
  std::ofstream options("pair-action-options.txt");
  for(size_t ia=0;ia<states.size();ia++)for(size_t ib=ia+1;ib<states.size();ib++){
    int a=states[ia],b=states[ib];if(a==95||b==95||a==96||b==96)continue;
    std::array<std::vector<Row>,2>choices;
    for(int bit=0;bit<2;bit++){
      for(auto ra:possible[a*2+bit])for(auto rb:possible[b*2+bit]){
        if(ra.t==b)ra.t=a;if(rb.t==b)rb.t=a;
        if(ra==rb && std::find(choices[bit].begin(),choices[bit].end(),ra)==choices[bit].end())choices[bit].push_back(ra);
      }
    }
    if(choices[0].empty()||choices[1].empty())continue;
    candidate_pairs++;options<<a<<" "<<b<<" "<<choices[0].size()<<" "<<choices[1].size()<<"\n";options.flush();
    for(auto r0:choices[0])for(auto r1:choices[1]){
      Table N=T;N[a][0]=r0;N[a][1]=r1;
      for(int q:states)if(q!=b)for(int bit=0;bit<2;bit++)if(N[q][bit].t==b)N[q][bit].t=a;
      bool ok=true;fulltests++;
      for(int ci=0;ci<nc;ci++)if(!execute(N,cs[ci])){ok=false;break;}
      if(!ok)continue;
      survivors++;std::string path="candidate-common-"+std::to_string(a)+"-"+std::to_string(b)+"-"+std::to_string(survivors)+".tm";std::ofstream out(path);out<<"#! start 95\n";
      for(int q:states)if(q!=b)for(int bit=0;bit<2;bit++){auto r=N[q][bit];out<<q<<" "<<bit<<" "<<r.w<<" "<<(r.d==1?'R':'L')<<" "<<r.t<<"\n";}
      std::cerr<<"SURVIVOR "<<a<<" "<<b<<" row0 "<<r0.w<<" "<<r0.d<<" "<<r0.t<<" row1 "<<r1.w<<" "<<r1.d<<" "<<r1.t<<"\n";
    }
  }
  std::ofstream summary("common-action-summary.json");summary<<"{\"candidate_pairs\":"<<candidate_pairs<<",\"combined_tables_tested\":"<<fulltests<<",\"survivors\":"<<survivors<<",\"cases\":"<<nc<<",\"distinct_windows\":"<<nw<<",\"window_cells\":"<<WIDTH<<",\"join_horizon\":"<<HORIZON<<",\"includes_halt_targets\":true,\"finite_only\":true}\n";
  std::cerr<<"Finished "<<candidate_pairs<<" candidate pairs; "<<fulltests<<" full tests; "<<survivors<<" survivors\n";
}
