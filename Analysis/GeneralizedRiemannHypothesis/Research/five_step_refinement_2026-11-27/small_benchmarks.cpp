#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <vector>
using namespace std;
using V=array<int,2>;
using K=array<int,3>;
void run(int p){
  vector<V> vs{{0,0}};
  for(int x=0;x<=(p-1)/2;x++)for(int y=0;y<p;y++)
    if(x!=0||(y>0&&y<=(p-1)/2))vs.push_back({x,y});
  const int N=vs.size();
  auto tag=[p](int a,int b,int c){return (a*p+b)*p+c;};
  vector<K> ks;vector<int> lookup(p*p*p,-1);
  for(int i=0;i<N;i++){
    auto [x,y]=vs[i];K k{x*x%p,x*y%p,y*y%p};
    auto [a,b,c]=k;assert(lookup[tag(a,b,c)]<0);
    lookup[tag(a,b,c)]=i;ks.push_back(k);
  }
  vector<array<int,6>> P(p);for(int i=0;i<p;i++){P[i][0]=1;int x=i*i%p;for(int j=1;j<=5;j++)P[i][j]=P[i][j-1]*x%p;}
  vector<vector<int>> pow4(N,vector<int>(p+1));
  for(int i=0;i<N;i++)for(int t=0;t<=p;t++){
    auto [x,y]=vs[i];pow4[i][t]=P[t==p?y:(x+t*y)%p][2];
  }
  const int e=lookup[tag(1,0,0)],f=lookup[tag(0,0,1)];
  int max0=0,max1=0,maxs=0;array<int,3> W{};
  long long n=0,nz=0;
  for(int i=0;i<N;i++){
    auto [a,b,c]=ks[i];
    for(int j=i;j<N;j++){
      auto [d,u,v]=ks[j];
      int x=2*p-1-a-d,y=2*p-b-u,z=2*p-1-c-v;
      if(x>=p)x-=p;
      if(y>=p)y-=p;
      if(y>=p)y-=p;
      if(z>=p)z-=p;
      int k=lookup[tag(x,y,z)];
      if(k<j)continue;
      ++n;if(i)++nz;
      int A=4*(p+1);
      for(int t=0;t<=p;t++){
        if((pow4[e][t]+pow4[f][t]+pow4[i][t]+pow4[j][t]+pow4[k][t])%p)continue;
        array<int,5> a{t==p?0:1,t==p?1:t};
        int h=2;
        for(int q:{i,j,k}){auto [x,y]=vs[q];a[h++]=t==p?y:(x+t*y)%p;}
        for(int r=3;r<=5;r++){
          int s=0; for(int v:a)s+=P[v][r];
          if(s%p){A+=2*(r-2);break;}
          assert(r<5);
        }
      }
      max0=max(max0,A);if(i)max1=max(max1,A);
      if(i&&i<j&&j<k&&i!=e&&i!=f&&j!=e&&j!=f&&k!=e&&k!=f&&A>maxs){
        maxs=A;W={i,j,k};
      }
    }
  }
  assert(maxs>2*(p+1)+16);
  cout<<p<<" "<<n<<"/"<<nz<<" "<<max0<<"/"<<max1<<"/"<<maxs;
  for(int i:W)cout<<" ("<<vs[i][0]<<","<<vs[i][1]<<")";
  cout<<endl;
}
int main(){for(int p:{103,107,109,113,127,137,139,149,151,157,163,167,173,179,181})run(p);}
