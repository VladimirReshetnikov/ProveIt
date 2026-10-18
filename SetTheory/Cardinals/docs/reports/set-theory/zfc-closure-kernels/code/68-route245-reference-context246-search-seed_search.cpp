#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

// A bounded discovery search, never used as evidence for non-halting.
// Accepts only a complete well-formed root frame with zero formula fields.
struct Action {int w,d,t;};
using Table=std::array<std::array<Action,2>,256>;
constexpr int LO=-131070, HI=131070, OFFSET=131072;
struct Result {bool pass=false; int64_t steps=0; int h=0,header=0,q=0; std::vector<int> vals;};
Result run(const Table& tab, int start, int64_t limit) {
  std::vector<uint8_t> mem(262145,0); auto at=[&](int p)->uint8_t& {return mem[p+OFFSET];};
  int q=start,h=0,l=0,r=-1;
  for(int64_t tm=0; tm<=limit; ++tm) {
    if(q==254) return {false,tm,h,0,q,{}};
    if(q==96 && l==h-1 && at(h-1)) {
      int header=h; while(header<=r && !at(header))++header;
      if(header>=h+40 && header<=r) {
        int p=header+1; std::vector<int> vs;
        while(p<r && !at(p) && at(p+1)) {
          int st=++p; while(p<=r && at(p))++p;
          vs.push_back(p-st-1);
        }
        if(p>r && vs.size()>=10 && vs[0]==0 && vs[2]==0 && vs[7]==0)
          return {true,tm,h,header,q,vs};
      }
    }
    Action a=tab[q][at(h)]; at(h)=a.w;
    if(a.w) {if(r<l)l=r=h;else{l=std::min(l,h);r=std::max(r,h);}}
    else if(r>=l) {
      if(h==l) {while(l<=r && !at(l)) ++l;}
      if(h==r) {while(r>=l && !at(r)) --r;}
    }
    h+=a.d;q=a.t;
    if(h<LO || h>HI) return {false,tm,h,0,q,{}};
  }
  return {false,limit,h,0,q,{}};
}
int main(int argc,char**argv) {
  if(argc<3){std::cerr<<"usage: seed_search table limit [start|seed] [w] [d]\n";return 2;}
  Table tab{};std::vector<int> states;std::ifstream in(argv[1]);std::string line;
  while(std::getline(in,line)) {if(line.empty()||line[0]=='#')continue;std::istringstream s(line);int q,b,w,t;char d;s>>q>>b>>w>>d>>t;tab[q][b]={w,d=='R'?1:-1,t};if(!b)states.push_back(q);}
  tab[255][0]={1,-1,255}; states.erase(std::remove(states.begin(),states.end(),97),states.end());
  std::string mode=argc>3?argv[3]:"seed";int w=argc>4?atoi(argv[4]):1;int d=argc>5?atoi(argv[5]):1;int64_t limit=std::stoll(argv[2]);
  if(mode=="core246") {
    tab[60][0].t=20;
    for(int dead:{0,1,3})states.erase(std::remove(states.begin(),states.end(),dead),states.end());
  }
  int cases=0,passes=0;
  for(int target:states) {
    if(mode=="seed")tab[0][0]={w,d,target};
    Result ans=run(tab,mode=="seed"?0:target,limit);++cases;
    if(ans.pass) {++passes;std::cout<<"PASS mode="<<mode<<" w="<<w<<" d="<<d<<" target="<<target<<" steps="<<ans.steps<<" h="<<ans.h<<" header="<<ans.header<<" values=";for(int i=0;i<9;++i)std::cout<<ans.vals[i]<<",";std::cout<<" spares="<<ans.vals.size()-9<<std::endl;}
  }
  std::cout<<"DONE cases="<<cases<<" passes="<<passes<<" limit="<<limit<<std::endl;
}
