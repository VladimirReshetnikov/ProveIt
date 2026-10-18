// Literal bounded execution for breakthrough_permutation_census.py.
// Each iteration executes exactly one row; no register-box summaries are used.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

struct Row { int write=0, delta=0, target=-1, selector=-1; };
int main(int argc, char** argv) {
  if (argc != 4) throw std::runtime_error("table permutations positive-step-limit");
  const long long lim=std::stoll(argv[3]);
  if (lim<1 || lim>10000000) throw std::runtime_error("limit outside 1..10000000");
  std::ifstream in(argv[1]), perms(argv[2]);
  if (!in || !perms) throw std::runtime_error("input open failed");
  std::array<std::array<Row,2>,255> original;
  int q,b,w,d,t,s, count=0;
  while(in>>q>>b>>w>>d>>t>>s) {
    if(q<0 || q>=254 || b<0 || b>1 || w<0 || w>1 || (d!=1 && d!=-1)
       || t<0 || t>254 || s< -1 || s>8 || original[q][b].target!=-1)
      throw std::runtime_error("invalid input row");
    original[q][b]={w,d,t,s}; ++count;
  }
  if(count<2 || count>508 || count%2) throw std::runtime_error("invalid row count");
  const std::array<int,9> skip={60,44,31,56,38,40,28,64,69};
  // One cell beyond each possible endpoint is available for safe lookahead.
  const long long origin=lim+3;
  std::vector<unsigned char> tape(2*lim+9,0);
  std::array<int,9> perm;
  int index=0;
  while(perms>>perm[0]) {
    for(int i=1;i<9;++i) if(!(perms>>perm[i])) throw std::runtime_error("short permutation");
    auto sorted=perm; std::sort(sorted.begin(),sorted.end());
    for(int i=0;i<9;++i) if(sorted[i]!=i) throw std::runtime_error("not a permutation");
    auto table=original;
    for(auto& rows:table) for(auto& row:rows)
      if(row.selector>=0) row.target=skip[perm[row.selector]];
    std::fill(tape.begin(),tape.end(),0);
    // Literal blank start: no prepared marks and no omitted prefix.
    int state=64; long long head=origin, lo=origin, hi=origin, steps=0;
    // Starts directly on the completely blank tape in old state 64.
    bool found=false; std::vector<long long> regs;
    for(;;) {
      if(state==96 && tape[head-1]) {
        long long first=lo; while(first<=hi && !tape[first]) ++first;
        if(first==head-1) {
          long long header=head; while(header<=hi && !tape[header]) ++header;
          if(header<=hi && header-head>=40) {
            long long last=hi; while(last>=lo && !tape[last]) --last;
            long long cursor=header+1; regs.clear(); bool shape=true;
            while(cursor<=last) {
              if(tape[cursor]) { shape=false; break; }
              ++cursor; long long value=0;
              while(cursor<=last && tape[cursor]) {++value; ++cursor;}
              if(!value) {shape=false; break;}
              regs.push_back(value-1);
            }
            if(shape && regs.size()>=9) {found=true; break;}
          }
        }
      }
      if(state==254 || steps==lim) break;
      const auto row=table[state][tape[head]];
      if(row.target<0) throw std::runtime_error("entered removed state");
      tape[head]=row.write; head+=row.delta; state=row.target; ++steps;
      lo=std::min(lo,head); hi=std::max(hi,head);
    }
    long long ones=0; std::uint64_t digest=14695981039346656037ULL;
    for(long long i=lo;i<=hi;++i) if(tape[i]) {
      ++ones;
      // Stable byte-wise FNV1a of each signed position in little-endian 64bits.
      const auto position=static_cast<std::uint64_t>(i-origin);
      for(int j=0;j<8;++j) {digest^=(position>>(8*j))&255; digest*=1099511628211ULL;}
    }
    std::cout<<"{\"index\":"<<index++<<",\"steps\":"<<steps<<",\"state\":"<<state
      <<",\"head\":"<<head-origin<<",\"one_count\":"<<ones<<",\"ones_fnv64\":\""
      <<digest<<"\",\"outcome\":\""<<(found?"structural_root":state==254?"halt":"fuel_limit")<<"\"";
    if(found) {
      std::cout<<",\"whole_one_positions\":["; bool first=true;
      for(long long i=lo;i<=hi;++i) if(tape[i]) {if(!first) std::cout<<','; first=false; std::cout<<i-origin;}
      std::cout<<']';
    }
    std::cout<<"}\n";
  }
  if(!perms.eof()) throw std::runtime_error("malformed permutation input");
}
