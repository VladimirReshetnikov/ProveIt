// Literal cache-MP bootstrap census. Adapted from ProveIt's
// breakthrough_permutation_census.cpp at 43026ff42f0939f09b9e95495248cfadcad38e38.
// Every microstep executes a literal binary row. No register-box summaries.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

struct Row { int write=0, delta=0, target=-1, selector=-1; };
using Nat=long long;

std::pair<Nat,Nat> unpair(Nat n) {
  Nat low=0,high=n+1;
  while(low+1<high) { Nat mid=(low+high)/2; if(mid*(mid+1)/2<=n) low=mid;else high=mid; }
  Nat b=n-low*(low+1)/2;return {low-b,b};
}
bool formula(Nat n,int fuel=256) {
  if(n==0) return true;
  if(fuel==0) return false;
  auto [a,b]=unpair(n/4);
  switch(n%4) {
    case 3:return a==b;
    case 2:return formula(b,fuel-1);
    case 0:return a==b || a==1 || formula(b,fuel-1);
    default:return false;
  }
}
bool good(Nat n) {
  for(int count=0;n && count<256;++count) {
    auto [a,b]=unpair(n);
    if(!formula(a) || b>=n) return false;
    n=b;
  }
  return n==0;
}

int main(int argc,char** argv) {
  if(argc!=4) throw std::runtime_error("rows permutations positive-step-limit");
  Nat lim=std::stoll(argv[3]);
  if(lim<1 || lim>10000000) throw std::runtime_error("limit outside1..10000000");
  std::ifstream in(argv[1]),perms(argv[2]);
  if(!in || !perms) throw std::runtime_error("input open failed");
  std::array<std::array<Row,2>,255> original;
  int q,b,w,d,t,s,count=0;
  while(in>>q>>b>>w>>d>>t>>s) {
    if(q<0 || q>=254 || b<0 || b>1 || w<0 || w>1 || (d!=1 && d!=-1)
       || t<0 || t>254 || s< -1 || s>8 || original[q][b].target!=-1)
      throw std::runtime_error("invalid input row");
    original[q][b]={w,d,t,s};++count;
  }
  if(count%2 || count<2) throw std::runtime_error("invalid working-state count");
  for(int i=0;i<254;++i) {
    if((original[i][0].target<0)!=(original[i][1].target<0)) throw std::runtime_error("partial state");
    for(const Row& row:original[i]) if(row.target>=0 && row.target!=254 && original[row.target][0].target<0)
      throw std::runtime_error("dangling transition");
  }
  const std::array<int,9> skip={60,44,31,56,38,40,28,64,69};
  const std::array<int,9> currentPhysical={6,2,0,4,3,7,8,5,1};
  const Nat origin=lim+3;
  std::vector<unsigned char> tape(2*lim+9,0);
  std::array<int,9> perm;
  int index=0;
  while(perms>>perm[0]) {
    for(int i=1;i<9;++i) if(!(perms>>perm[i])) throw std::runtime_error("short permutation");
    auto sorted=perm;std::sort(sorted.begin(),sorted.end());
    for(int i=0;i<9;++i) if(sorted[i]!=i) throw std::runtime_error("not a permutation");
    auto table=original;
    for(auto& pair:table) for(auto& row:pair) if(row.selector>=0) row.target=skip[perm[row.selector]];
    std::fill(tape.begin(),tape.end(),0);
    int state=1;
    Nat head=origin,lo=origin,hi=origin+1,steps=0,structuralCount=0,foundGap=-1;
    tape[origin+1]=1;
    bool found=false;
    std::vector<Nat> regs,foundRegs;
    for(;;) {
      if(state==96 && tape[head-1]) {
        Nat first=lo;while(first<=hi && !tape[first])++first;
        if(first==head-1) {
          Nat header=head;while(header<=hi && !tape[header])++header;
          if(header<=hi && header-head>=40) {
            Nat last=hi;while(last>=lo && !tape[last])--last;
            Nat cursor=header+1;regs.clear();bool shape=true;
            while(cursor<=last) {
              if(tape[cursor]) {shape=false;break;}
              ++cursor;Nat value=0;
              while(cursor<=last && tape[cursor]) {++value;++cursor;}
              if(!value) {shape=false;break;}
              regs.push_back(value-1);
            }
            if(shape && regs.size()>=9) {
              ++structuralCount;
              if(formula(regs[perm[currentPhysical[1]]]) && formula(regs[perm[currentPhysical[5]]])
                  && good(regs[perm[currentPhysical[2]]])) {
                found=true;foundGap=header-head;foundRegs=regs;break;
              }
            }
          }
        }
      }
      if(state==254 || steps==lim) break;
      const Row& row=table[state][tape[head]];
      if(row.target<0) throw std::runtime_error("entered removed state");
      tape[head]=row.write;head+=row.delta;state=row.target;++steps;
      lo=std::min(lo,head);hi=std::max(hi,head);
    }
    Nat ones=0;std::uint64_t digest=14695981039346656037ULL;
    for(Nat i=lo;i<=hi;++i) if(tape[i]) {
      ++ones;auto pos=static_cast<std::uint64_t>(i-origin);
      for(int j=0;j<8;++j) {digest^=(pos>>(8*j))&255;digest*=1099511628211ULL;}
    }
    std::cout<<"{\"index\":"<<index++<<",\"steps\":"<<steps<<",\"state\":"<<state
      <<",\"head\":"<<head-origin<<",\"one_count\":"<<ones<<",\"ones_fnv64\":\""<<digest
      <<"\",\"structural_roots_seen\":"<<structuralCount<<",\"outcome\":\""
      <<(found?"safe_root":state==254?"halt":"fuel_limit")<<"\"";
    if(found) {
      std::cout<<",\"gap\":"<<foundGap<<",\"values\":[";
      for(std::size_t i=0;i<foundRegs.size();++i) {if(i)std::cout<<',';std::cout<<foundRegs[i];}
      std::cout<<"],\"whole_one_positions\":[";bool first=true;
      for(Nat i=lo;i<=hi;++i) if(tape[i]) {if(!first)std::cout<<',';first=false;std::cout<<i-origin;}
      std::cout<<']';
    }
    std::cout<<"}\n";
    if(index%512==0) std::cerr<<"completed "<<index<<" permutations\n";
  }
  if(!perms.eof()) throw std::runtime_error("malformed permutation input");
}
