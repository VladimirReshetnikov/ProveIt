#include "core_enumeration.hpp"
#include <fstream>
#include <iostream>
int main(int argc,char**argv){
 try{
  std::ofstream list(argc>1?argv[1]:"cores.csv");
  std::ofstream stats(argc>2?argv[2]:"core_counts.csv");
  if(!list||!stats)throw std::runtime_error("cannot open output files");
  list<<"m,family,n,cells\n";
  stats<<"m,n,all_antichains,labelled_cores,degree_sorted_cores,core_orbits\n";
  const std::array<shuffleproof::U,7> expected={2,3,6,20,168,7581,7828354};
  for(unsigned m=2;m<=6;m++){
   shuffleproof::Enumeration e(m);e.run();
   if(e.total()!=expected[m])throw std::runtime_error("antichain count sanity check failed");
   std::cerr<<m<<" rows: "<<e.total()<<" antichains, "
            <<e.representatives.size()<<" core orbits\n";
   for(auto f:e.representatives){
    unsigned cells=0;
    for(auto z=f;z;z&=z-1)cells+=std::popcount(static_cast<unsigned>(std::countr_zero(z)));
    list<<m<<","<<f<<","<<std::popcount(f)<<","<<cells<<"\n";
   }
   for(unsigned n=0;n<65;n++)if(e.counts[n]){
    unsigned c=0;for(auto f:e.representatives)if(static_cast<unsigned>(std::popcount(f))==n)c++;
    stats<<m<<","<<n<<","<<e.counts[n]<<","<<e.labelled_cores[n]
         <<","<<e.sorted_cores[n]<<","<<c<<"\n";
   }
  }
 }catch(const std::exception &e){std::cerr<<e.what()<<"\n";return 1;}
}
