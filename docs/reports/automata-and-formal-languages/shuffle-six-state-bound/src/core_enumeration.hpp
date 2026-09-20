#ifndef SHUFFLE_CORE_ENUMERATION_HPP
#define SHUFFLE_CORE_ENUMERATION_HPP
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <set>
#include <stdexcept>
#include <vector>
namespace shuffleproof {
using U=std::uint64_t;
struct Enumeration {
 unsigned m,N;
 std::array<U,64> incomparable{};
 std::array<U,6> hasrow{};
 std::vector<std::array<unsigned,64>> permutations;
 std::array<U,65> counts{},labelled_cores{},sorted_cores{};
 std::set<U> representatives;
 U singletons=0;
 explicit Enumeration(unsigned rows):m(rows),N(0) {
  if(m<1||m>6)throw std::invalid_argument("row count must be 1 through 6");
  N=1U<<m;
  for(unsigned a=0;a<N;a++)for(unsigned b=0;b<N;b++)
   if((a&b)!=a&&(a&b)!=b)incomparable[a]|=U(1)<<b;
  for(unsigned r=0;r<m;r++){
   singletons|=U(1)<<(1U<<r);
   for(unsigned a=0;a<N;a++)if(a&(1U<<r))hasrow[r]|=U(1)<<a;
  }
  std::vector<unsigned> p(m);for(unsigned r=0;r<m;r++)p[r]=r;
  do{
   std::array<unsigned,64> q{};
   for(unsigned a=0;a<N;a++)for(unsigned r=0;r<m;r++)
    if(a&(1U<<r))q[a]|=1U<<p[r];
   permutations.push_back(q);
  }while(std::next_permutation(p.begin(),p.end()));
 }
 void visit(U family,U allowed,unsigned k){
  ++counts[k];
  if(k>=m && !(family&singletons) && !(family&1)){
   std::array<int,6> degree{};bool ok=true;
   for(unsigned r=0;r<m;r++){
    degree[r]=std::popcount(family&hasrow[r]);
    if(degree[r]<2)ok=false;
   }
   if(ok)for(unsigned r=0;r<m;r++)for(unsigned s=0;s<m;s++)
    if(r!=s && !(family&hasrow[r]&~hasrow[s]))ok=false;
   if(ok){
    ++labelled_cores[k];
    if(std::is_sorted(degree.begin(),degree.begin()+m)){
     ++sorted_cores[k];U best=family;
     for(const auto &p:permutations){
      bool preserve=true;
      for(unsigned r=0;r<m;r++)
       if(degree[r]!=degree[std::countr_zero(p[1U<<r])]){
        preserve=false;break;
       }
      if(!preserve)continue;
      U image=0;
      for(U z=family;z;z&=z-1)image|=U(1)<<p[std::countr_zero(z)];
      best=std::min(best,image);
     }
     representatives.insert(best);
    }
   }
  }
  while(allowed){
   unsigned v=std::countr_zero(allowed);allowed&=allowed-1;
   visit(family|(U(1)<<v),allowed&incomparable[v],k+1);
  }
 }
 void run(){visit(0,N==64?~U(0):(U(1)<<N)-1,0);}
 U total()const{U n=0;for(U c:counts)n+=c;return n;}
};
}
#endif
