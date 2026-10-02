#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>
using namespace std;
using Poly=array<uint64_t,13>;
int main(int argc,char**argv){
 bool king=string(argv[1])=="king"; int n=atoi(argv[2]),K=atoi(argv[3]),B=1<<n;
 vector<int> masks,pc(B);for(int s=0;s<B;s++){pc[s]=__builtin_popcount((unsigned)s);if(pc[s]<=K&&(!king||!(s&(s<<1))))masks.push_back(s);}
 unordered_map<int,Poly> dp,nd; dp[0][0]=1;
 for(int r=0;r<n;r++){
  nd.clear();nd.reserve(dp.size()*2);
  for(const auto& kv:dp){int a=kv.first&(B-1),b=kv.first>>n;int forbid=king?(a|(a<<1)|(a>>1)):((a<<2)|(a>>2)|(b<<1)|(b>>1));
   for(int c:masks) if(!(c&forbid)&&pc[c]+pc[a]+pc[b]<=K){
    int key=king?c:(c|(a<<n));auto &p=nd[key];int k=pc[c];for(int j=0;j+k<=K;j++)p[j+k]+=kv.second[j];
   }
  }
  dp.swap(nd);
 }
 Poly sum{};for(auto&kv:dp)for(int j=0;j<=K;j++)sum[j]+=kv.second[j];
 cout<<argv[1]<<" "<<n;for(int j=0;j<=K;j++)cout<<" "<<sum[j];cout<<endl;
}
