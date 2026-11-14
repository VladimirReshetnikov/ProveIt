#include <vector>
#include <array>
#include <fstream>
#include <iostream>
#include <cstdint>
using namespace std;
int main(int argc,char**argv){
 ifstream f(argv[1]);vector<array<int,4>> cfg;array<int,4>x;while(f>>x[0]>>x[1]>>x[2]>>x[3])cfg.push_back(x);
 const int M=19683;int pw[9]={1};for(int i=1;i<9;++i)pw[i]=pw[i-1]*3;
 vector<uint8_t> seen((cfg.size()*M+7)/8);vector<int> queue;vector<int> reach(cfg.size()), nonzero(cfg.size()); vector<array<int,9>> masks(cfg.size());
 auto add=[&](int pc,int v){int k=pc*M+v;if(!(seen[k/8]&(1<<(k%8)))){seen[k/8]|=1<<(k%8);queue.push_back(k);}};
 int seed[9]={1,0,2,0,0,1,0,0,1},v=0;for(int i=0;i<9;++i)v+=seed[i]*pw[i];add(136,v);
 for(size_t pos=0;pos<queue.size();++pos){int pc=queue[pos]/M,v=queue[pos]%M; reach[pc]++; for(int j=0;j<9;j++) masks[pc][j] |= 1 << ((v/pw[j])%3); auto c=cfg[pc];int a=(v/pw[c[1]])%3;
  if(c[0]==0)add(c[2],v+(a<2?pw[c[1]]:0));
  else if(c[0]==1){if(a==0)add(c[2],v);else {nonzero[pc]++;add(c[3],v-pw[c[1]]);if(a==2)add(c[3],v);}}
  else if(c[0]==2)add(c[2],v);
 }
 ofstream g(argv[2]); for(int i=0;i<(int)cfg.size();i++){g<<i<<" "<<reach[i];for(int j=0;j<9;j++)g<<" "<<masks[i][j];g<<"\n";}
 cout<<"{\"abstract_states\":"<<queue.size()<<",\"unreachable_ordinals\":[";bool comma=false;for(int i=136;i<(int)cfg.size();++i)if(!reach[i]){if(comma)cout<<",";cout<<i;comma=true;}cout<<"],\"always_zero_CD\":[";comma=false;for(int i=0;i<(int)cfg.size();++i)if(cfg[i][0]==1&&reach[i]&&!nonzero[i]){if(comma)cout<<",";cout<<i;comma=true;}cout<<"]}\n";
}
