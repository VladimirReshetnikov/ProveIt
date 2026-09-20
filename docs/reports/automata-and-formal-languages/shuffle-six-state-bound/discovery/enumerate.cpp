#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <unordered_set>
#include <vector>
#include <chrono>
using U=uint64_t;
int m,M;
std::vector<std::array<int,6>> orders;
std::vector<std::array<int,64>> maps;
std::array<U,64> comp;
U canonical(U f){
 int deg[6]={};
 std::vector<int> masks;
 for(U u=f;u;u&=u-1){int a=__builtin_ctzll(u);masks.push_back(a);for(int i=0;i<m;++i)deg[i]+=(a>>i)&1;}
 U best=~U(0);
 for(size_t k=0;k<orders.size();++k){
  const auto&o=orders[k]; bool ok=true;
  for(int i=1;i<m;++i)if(deg[o[i-1]]>deg[o[i]]){ok=false;break;}
  if(!ok)continue;
  U z=0;for(int a:masks)z|=U(1)<<maps[k][a];
  if(z<best)best=z;
 }
 assert(best!=~U(0) || f==~U(0));
 return best;
}
bool hard(U f){
 if(!f)return false;
 U rows[6]={};int j=0;
 for(U u=f;u;u&=u-1,++j){int a=__builtin_ctzll(u); if(__builtin_popcount(a)<2)return false;for(int i=0;i<m;++i)if((a>>i)&1)rows[i]|=U(1)<<j;}
 for(int i=0;i<m;++i){
  if(__builtin_popcountll(rows[i])<2)return false;
  for(int k=0;k<m;++k)if(i!=k && (rows[i]&rows[k])==rows[i])return false;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc<3){std::cerr<<"usage: enumerate ROWS OUTPUT\n";return 2;}
 m=std::stoi(argv[1]);if(m<1||m>6)return 2;M=1<<m;
 std::array<int,6> o={0,1,2,3,4,5};
 do{
  orders.push_back(o);std::array<int,64> p={};
  for(int a=0;a<M;++a)for(int j=0;j<m;++j)if((a>>o[j])&1)p[a]|=1<<j;
  maps.push_back(p);
 }while(std::next_permutation(o.begin(),o.begin()+m));
 for(int a=0;a<M;++a){comp[a]=0;for(int b=0;b<M;++b)if((a&b)==a||(a&b)==b)comp[a]|=U(1)<<b;}
 U universe=M==64?~U(0):(U(1)<<M)-1;
 std::unordered_set<U> layer={0};std::ofstream out(argv[2]);
 int k=0;size_t total=0,total_hard=0;
 while(!layer.empty()){
  std::vector<U> sorted(layer.begin(),layer.end());std::sort(sorted.begin(),sorted.end());
  size_t h=0;for(U f:sorted){out<<m<<" "<<k<<" "<<f<<" "<<hard(f)<<"\n";h+=hard(f);}
  total+=layer.size();total_hard+=h;
  std::cerr<<m<<" rows "<<k<<" columns: "<<layer.size()<<" reps, "<<h<<" hard\n";
  std::unordered_set<U> next;
  for(U f:sorted){
   U banned=0;for(U u=f;u;u&=u-1)banned|=comp[__builtin_ctzll(u)];
   U choices=universe&~banned;
   for(U u=choices;u;u&=u-1){U bit=u&-u;next.insert(canonical(f|bit));}
  }
  layer=std::move(next);++k;
 }
 std::cerr<<"TOTAL "<<m<<" "<<total<<" HARD "<<total_hard<<"\n";
}
