#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <unordered_set>
#include <vector>
using U=uint64_t;
int m;
std::vector<std::vector<int>> perms;
std::vector<std::array<int,64>> maps;
std::array<U,64> incompatible;
U canonical(U x){
 std::vector<int> deg(m,0),masks;
 U z=x;while(z){int s=__builtin_ctzll(z);z&=z-1;masks.push_back(s);for(int i=0;i<m;i++)deg[i]+=(s>>i)&1;}
 auto target=deg;std::sort(target.begin(),target.end());
 U best=~U(0);
 for(size_t p=0;p<perms.size();p++){
  bool good=true;for(int i=0;i<m;i++)if(deg[i]!=target[perms[p][i]]){good=false;break;}
  if(!good)continue;
  U v=0;for(int s:masks)v|=U(1)<<maps[p][s];best=std::min(best,v);
 }
 return best;
}
bool hard(U x){
 std::vector<U> row(m,0);int j=0;
 while(x){int s=__builtin_ctzll(x);x&=x-1;if(__builtin_popcount(s)<2)return false;
  for(int i=0;i<m;i++)if((s>>i)&1)row[i]|=U(1)<<j;j++;}
 for(int i=0;i<m;i++){
  if(__builtin_popcountll(row[i])<2)return false;
  for(int k=0;k<m;k++)if(i!=k && (row[i]&~row[k])==0)return false;
 }
 return true;
}
int main(int argc,char**argv){
 std::ofstream out(argc>1?argv[1]:"targets.tsv");
 for(m=2;m<=6;m++){
  perms.clear();maps.clear();incompatible.fill(0);
  std::vector<int> p;for(int i=0;i<m;i++)p.push_back(i);
  int limit=1<<m;
  do{perms.push_back(p);std::array<int,64> a{};for(int s=0;s<limit;s++)for(int i=0;i<m;i++)if((s>>i)&1)a[s]|=1<<p[i];maps.push_back(a);}while(std::next_permutation(p.begin(),p.end()));
  for(int s=1;s<limit-1;s++)for(int t=1;t<limit-1;t++)if((s&t)==s || (s&t)==t)incompatible[s]|=U(1)<<t;
  std::unordered_set<U> level{0};size_t total=0,nhard=0;
  for(int n=0;!level.empty();n++){
   std::vector<U> ordered(level.begin(),level.end());std::sort(ordered.begin(),ordered.end());
   int counthard=0;for(U x:ordered){total++;if(hard(x)){out<<m<<'\t'<<x<<'\n';counthard++;}}
   nhard+=counthard;
   std::cerr<<m<<' '<<n<<' '<<level.size()<<' '<<counthard<<'\n';
   std::unordered_set<U> next;
   for(U x:ordered)for(int s=1;s<limit-1;s++)if(!(x&incompatible[s]))next.insert(canonical(x|(U(1)<<s)));
   level=std::move(next);
  }
  std::cerr<<"TOTAL "<<m<<' '<<total<<' '<<nhard<<'\n';
 }
}
