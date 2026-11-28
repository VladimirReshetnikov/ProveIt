// Exhaustive six-step rank-two check after normalizing an independent pair.
// Compile: c++ -O3 -std=c++17 verify_six.cpp -o verify_six
#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <vector>
#include <utility>
using namespace std;
using V=pair<int,int>;
int main(){
 for(int p:{13,17,19,23,29,31,37,41,43,47}){
  auto mod=[&](int a){a%=p;return a<0?a+p:a;};
  vector<V> pts;
  for(int x=0;x<p;x++)for(int y=0;y<p;y++)if(V{x,y}<=V{mod(-x),mod(-y)})pts.emplace_back(x,y);
  auto key=[&](int x,int y,int z){return (mod(x)*p+mod(y))*p+mod(z);};
  int N=pts.size(); vector<array<int,3>> quad(N);
  vector<vector<pair<int,int>>> pairs(p*p*p);
  for(int i=0;i<N;i++){auto [x,y]=pts[i];quad[i]={mod(x*x),mod(x*y),mod(y*y)};}
  for(int i=0;i<N;i++)for(int j=i;j<N;j++)pairs[key(quad[i][0]+quad[j][0],quad[i][1]+quad[j][1],quad[i][2]+quad[j][2])].emplace_back(i,j);
  vector<V> dirs;for(int z=0;z<p;z++)dirs.emplace_back(1,z);dirs.emplace_back(0,1);
  vector<vector<array<int,6>>> powers(N,vector<array<int,6>>(p+1));
  for(int i=0;i<N;i++)for(int u=0;u<=p;u++){int a=mod(pts[i].first*dirs[u].first+pts[i].second*dirs[u].second);int b=mod(a*a),c=1;for(int k=0;k<6;k++)powers[i][u][k]=c=mod(c*b);}
  auto idx=[&](V v){return int(find(pts.begin(),pts.end(),v)-pts.begin());};
  int b1=idx({1,0}),b2=idx({0,1});assert(b1<N&&b2<N);
  long long inspected=0,top=0;int best=-1,bestSimple=-1;array<int,4>witness{},simpleWitness{};
  for(int i=0;i<N;i++)for(int j=i;j<N;j++){
   int kkey=key(-1-quad[i][0]-quad[j][0],-quad[i][1]-quad[j][1],-1-quad[i][2]-quad[j][2]);
   for(auto [k,l]:pairs[kkey])if(j<=k){
    inspected++;array<int,6>a={b1,b2,i,j,k,l};int A=0,t=6;
    for(int u=0;u<=p;u++){
     int d=0;for(int z=0;z<6;z++){int sum=0;for(int h:a)sum+=powers[h][u][z];if(sum%p){d=z+1;break;}}
     assert(d>0);t=min(t,d);A+=2*d;
    }
    if(t==3){top++;assert((p-1)%6==0);for(int h:{i,j,k,l})assert(pts[h].first==0 || pts[h].second==0);assert(A==6*(p+1)+((p-1)%12==0?36:0));}
    assert(t<=3);
    if(A>best){best=A;witness={i,j,k,l};}
    auto sorted=a;sort(sorted.begin(),sorted.end());bool simple=sorted[0]!=0&&adjacent_find(sorted.begin(),sorted.end())==sorted.end();
    if(simple&&A>bestSimple){bestSimple=A;simpleWitness={i,j,k,l};}
   }
  }
  int nonzeroM1bound=2*(p+1)+4*((p-1)%12==0?5:4);
  assert(best>nonzeroM1bound&&bestSimple>nonzeroM1bound);
  if((p-1)%6==0){assert(top==1);assert(best==6*(p+1)+((p-1)%12==0?36:0));}
  else assert(top==0);
  cout<<"p="<<p<<" candidates="<<inspected<<" t=3="<<top<<" max="<<best<<" simple="<<bestSimple<<" simple-extra=";for(int i:simpleWitness)cout<<" ("<<pts[i].first<<","<<pts[i].second<<")";cout<<endl;
 }
}
