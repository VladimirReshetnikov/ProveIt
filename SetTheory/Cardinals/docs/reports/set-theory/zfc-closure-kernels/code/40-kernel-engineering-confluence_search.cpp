// Exhaustive one-transition surgery search on an observed partial-tape catalog.
// The search is heuristic until a candidate passes universal instruction checks.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <tuple>
#include <vector>
struct Row {int w,d,t;};
struct Pat {uint64_t bits, known;};
struct Conf {int q,h;uint64_t bits;bool operator==(const Conf&o)const{return q==o.q&&h==o.h&&bits==o.bits;}};
Row tab[255][2];
int width, fuel=32;
std::vector<Conf> path(int p,Pat a,int dead){
  std::vector<Conf> out; Conf s{p,width,a.bits};
  for(int k=0;k<fuel;k++){
    if(s.q==254||s.h<0||s.h>2*width||!(a.known>>s.h&1))break;
    auto row=tab[s.q][(s.bits>>s.h)&1];
    s.bits=(s.bits&~(1ull<<s.h))|(uint64_t(row.w)<<s.h);s.h+=row.d;s.q=row.t;
    if(s.q!=dead)out.push_back(s);
  }
  return out;
}
bool joins(int p,Pat a,Row first,int dead,const std::vector<Conf>&orig){
  if(first.t==dead)return false;
  Conf s{first.t,width+first.d,(a.bits&~(1ull<<width))|(uint64_t(first.w)<<width)};
  for(int k=0;k<fuel;k++){
    if(std::find(orig.begin(),orig.end(),s)!=orig.end())return true;
    if(s.q==dead||s.q==254||s.h<0||s.h>2*width||!(a.known>>s.h&1))return false;
    auto row=tab[s.q][(s.bits>>s.h)&1];
    if(row.t==dead)return false;
    s.bits=(s.bits&~(1ull<<s.h))|(uint64_t(row.w)<<s.h);s.h+=row.d;s.q=row.t;
  }
  return false;
}
int main(int argc,char**argv){
  if(argc>1&&std::string(argv[1])=="--self-test"){
    width=3;fuel=12;Pat a{0,127};
    tab[0][0]={0,1,1};tab[1][0]={0,-1,254};tab[2][0]={0,1,254};
    auto op=path(0,a,1);
    assert(joins(0,a,{0,-1,2},1,op)); // Same output, opposite first move.
    assert(!joins(0,a,{1,-1,2},1,op)); // Permanent wrong output is rejected.
    tab[3][0]={0,-1,4};tab[4][1]={0,1,5};tab[4][0]={0,1,1};tab[5][0]={0,-1,254};
    assert(joins(0,a,{1,1,3},1,op)); // Changed write, restored four steps later.
    assert(!joins(0,a,{0,1,3},1,op)); // This route needs the changed write.
    assert(!joins(0,a,{0,1,1},1,op)); // Deleted state is always forbidden.
    Pat missing_left{0,127^(1ull<<2)};
    assert(!joins(0,missing_left,{0,-1,2},1,op)); // Unknown read cannot certify.
    std::cout<<"PASS: opposite-move confluence, restored-write confluence, wrong-tape rejection, necessary-write control, deleted-state rejection, unknown-read rejection\n";
    return 0;
  }
  if(argc>1)fuel=std::stoi(argv[1]);
  std::ifstream in("contexts_search.txt"); int nr;
  in>>width>>nr;
  for(int i=0;i<nr;i++){int q,b,w,d,t;in>>q>>b>>w>>d>>t;tab[q][b]={w,d,t};}
  int nc;in>>nc; std::map<std::pair<int,int>,std::vector<Pat>> cats;
  for(int j=0;j<nc;j++){
    int p,b,k;in>>p>>b>>k;auto &v=cats[{p,b}];
    for(int x=0;x<k;x++){std::string s;in>>s;uint64_t bits=0,known=0;for(int i=0;i<int(s.size());i++){if(s[i]!='2')known|=1ull<<i;if(s[i]=='1')bits|=1ull<<i;}v.push_back({bits,known});}
  }
  int nq;in>>nq; int total=0,all=0;long long tested=0;
  for(int j=0;j<nq;j++){
    int dead,ni;in>>dead>>ni;std::vector<std::pair<int,int>>inc(ni);for(auto &e:inc)in>>e.first>>e.second;
    bool allok=true;std::vector<std::tuple<int,int,std::vector<Row>>>found;
    for(auto [p,b]:inc){
      auto &ps=cats[{p,b}];std::vector<Row> cand;
      if(ps.empty()){allok=false;continue;}
      auto orig=path(p,ps[0],dead);
      for(int w=0;w<2;w++)for(int d:{-1,1})for(int t=0;t<255;t++){
        if(t==8||t==dead)continue;tested++;
        Row r{w,d,t};if(joins(p,ps[0],r,dead,orig))cand.push_back(r);
      }
      for(int i=1;i<int(ps.size())&&!cand.empty();i++){
        auto op=path(p,ps[i],dead);
        cand.erase(std::remove_if(cand.begin(),cand.end(),[&](Row r){return !joins(p,ps[i],r,dead,op);}),cand.end());
      }
      if(cand.empty()){std::cerr<<dead<<'\t'<<p<<'\t'<<b<<'\t'<<ps.size()<<"\t0\n";allok=false;break;}
      found.push_back({p,b,cand});
    }
    if(allok){all++;std::cout<<"DELETE "<<dead<<" INCOMING "<<ni<<"\n";for(auto &[p,b,cs]:found){std::cout<<p<<' '<<b<<" =>";for(auto r:cs)std::cout<<" ("<<r.w<<','<<r.d<<','<<r.t<<')';std::cout<<'\n';}std::cout.flush();}
    total++;
  }
  std::cout<<"SUMMARY states="<<total<<" tested="<<tested<<" successful="<<all<<" radius="<<width<<" fuel="<<fuel<<"\n";
}
