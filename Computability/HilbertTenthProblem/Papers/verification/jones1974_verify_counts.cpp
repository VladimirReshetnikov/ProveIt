// Jones (1974), Table 1: exhaustive finite counts for n=1,2,3.
// Self-contained (reads no article source).
// Build: c++ -O3 -std=c++17 jones1974_verify_counts.cpp -o jones1974_verify_counts
// Run: ./jones1974_verify_counts
// A cutoff by itself does NOT rule out later halts. Completeness here is
// conditional on the established SH(1)=1, SH(2)=6, SH(3)=21 bounds.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iomanip>
#include <iostream>
struct Rule { int write, direction, next; };
int main() {
  const std::array<int,4> bounds{0,1,6,21};
  const std::array<std::uint64_t,4> expectedH{0,32,9784,7571840};
  const std::array<int,4> expectedSigma{0,1,4,6}, expectedSC{0,1,4,7};
  for (int n=1;n<=3;++n) {
    const unsigned base=4*(n+1);
    std::uint64_t total=1;
    for(int j=0;j<2*n;++j) total*=base;
    std::uint64_t halts=0;
    int sigma=0, sc=0, sh=0;
    for(std::uint64_t id=0;id<total;++id) {
      auto code=id; std::array<Rule,6> rules{};
      for(int j=0;j<2*n;++j) {
        unsigned d=code%base; code/=base;
        rules[j]={int(d%2),(d/2)%2 ? 1 : -1,int(d/4)};
      }
      std::uint64_t tape=0;
      int q=1,head=32,lo=32,hi=32;
      for(int step=1;step<=bounds[n];++step) {
        lo=std::min(lo,head); hi=std::max(hi,head);
        const auto mask=std::uint64_t{1}<<head;
        auto r=rules[2*(q-1)+((tape&mask)?1:0)];
        tape=r.write ? tape|mask : tape&~mask;
        head+=r.direction; q=r.next;
        if(q==0) {
          ++halts;
          int ones=0; for(auto t=tape;t;t&=t-1) ++ones;
          sigma=std::max(sigma,ones);
          sc=std::max(sc,hi-lo+1); sh=std::max(sh,step);
          break;
        }
      }
    }
    assert(halts==expectedH[n] && sigma==expectedSigma[n]);
    assert(sc==expectedSC[n] && sh==bounds[n]);
    std::cout << "n=" << n << ": " << total << " labelled tables; "
              << halts << " halts witnessed by shift " << bounds[n]
              << "; Sigma=" << sigma << "; SC=" << sc << "; SH=" << sh
              << "; H/N=" << std::fixed << std::setprecision(9)
              << static_cast<double>(halts)/total << '\n';
  }
  std::cout << "PASS (finite enumeration; see stated cutoff qualification).\n";
}
