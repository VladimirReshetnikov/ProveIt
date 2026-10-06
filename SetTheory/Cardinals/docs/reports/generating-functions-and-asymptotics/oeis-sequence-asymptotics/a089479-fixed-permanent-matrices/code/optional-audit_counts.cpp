#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <vector>
using namespace std;
int main(){
  ofstream out("audit_counts.tsv"); out<<"mode\tn\tk\tcount\n";
  for(int diagonal=0;diagonal<=1;diagonal++) for(int n=1;n<=(diagonal?5:5);n++){
    int pos[6][6],q=0;
    for(int i=0;i<n;i++)for(int j=0;j<n;j++)pos[i][j]=(diagonal&&i==j)?-1:q++;
    vector<int> a(1u<<q,0); vector<int> perm(n); iota(perm.begin(),perm.end(),0);
    do{unsigned mask=0;for(int i=0;i<n;i++)if(pos[i][perm[i]]>=0)mask|=1u<<pos[i][perm[i]];a[mask]++;}while(next_permutation(perm.begin(),perm.end()));
    for(int bit=0;bit<q;bit++)for(unsigned mask=0;mask<a.size();mask++)if(mask&(1u<<bit))a[mask]+=a[mask^(1u<<bit)];
    map<int,long long> counts,strong;
    for(unsigned mask=0;mask<a.size();mask++){
      counts[a[mask]]++;
      if(diagonal){
        unsigned reach[6]; for(int i=0;i<n;i++){reach[i]=1u<<i;for(int j=0;j<n;j++)if(pos[i][j]>=0&&(mask&(1u<<pos[i][j])))reach[i]|=1u<<j;}
        for(int t=0;t<n;t++)for(int i=0;i<n;i++)if(reach[i]&(1u<<t))reach[i]|=reach[t];
        bool isstrong=true;for(int i=0;i<n;i++)if(reach[i]!=(1u<<n)-1)isstrong=false;
        if(isstrong)strong[a[mask]]++;
      }
    }
    for(auto [k,c]:counts)out<<(diagonal?"diagonal_one":"all_binary")<<'\t'<<n<<'\t'<<k<<'\t'<<c<<'\n';
    for(auto [k,c]:strong)out<<"strong"<<'\t'<<n<<'\t'<<k<<'\t'<<c<<'\n';
    cerr<<"Done "<<diagonal<<" "<<n<<" objects "<<a.size()<<"\n";
  }
}
