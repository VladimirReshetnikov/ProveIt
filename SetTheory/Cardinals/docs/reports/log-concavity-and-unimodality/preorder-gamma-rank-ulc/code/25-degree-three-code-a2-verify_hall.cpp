// Independent labeled-support counter, using Hall's theorem only.
// Input: graph count; then n followed by n off-diagonal relation row masks.
// Output: number of disjoint ordered (A,B), |A|=|B|=k, satisfying Hall,
// for k=0,1,2,3,4.  No perfect-match recursion or production code is used.
#include <iostream>
#include <vector>
#include <array>
#include <cstdint>
using namespace std;
int main(){
 ios::sync_with_stdio(false);cin.tie(nullptr);
 int instances;if(!(cin>>instances))return 1;
 while(instances--){
  int n;cin>>n;if(n>20)return 2;
  vector<unsigned> row(n);unsigned sources=0;
  for(int i=0;i<n;i++){cin>>row[i];if(row[i])sources|=1u<<i;}
  const unsigned limit=1u<<n;
  vector<unsigned> nbr(limit,0);
  vector<unsigned char> cardinality(limit,0);
  for(unsigned x=1;x<limit;x++){
   unsigned low=x&-x;unsigned prev=x-low;
   nbr[x]=nbr[prev]|row[__builtin_ctz(low)];
   cardinality[x]=cardinality[prev]+1;
  }
  array<uint64_t,5> count{1,0,0,0,0};
  // B may only contain neighbors of A and must be disjoint from A.
  // Enumerating all k-element submasks gives every labeled support exactly once.
  for(unsigned a=sources;a;a=(a-1)&sources){
   int k=cardinality[a];if(k>4)continue;
   unsigned available=nbr[a]&~a;
   if(cardinality[available]<k)continue;
   vector<unsigned> proper;
   for(unsigned s=(a-1)&a;s;s=(s-1)&a)proper.push_back(s);
   for(unsigned b=available;b;b=(b-1)&available){
    if(cardinality[b]!=k)continue;
    bool hall=true;
    for(unsigned s:proper){
     if(cardinality[nbr[s]&b]<cardinality[s]){hall=false;break;}
    }
    if(hall)count[k]++;
   }
  }
  for(int k=0;k<=4;k++)cout<<count[k]<<(k==4?'\n':' ');
 }
}
