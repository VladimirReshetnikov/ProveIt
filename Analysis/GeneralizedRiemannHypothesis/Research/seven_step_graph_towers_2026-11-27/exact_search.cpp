#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>
using namespace std;
using U=uint64_t;
using K=array<int,8>;
K key(int x,int y,int p) {
  int a=x*x%p,b=x*y%p,c=y*y%p;
  return {a,b,c,a*a%p,a*b%p,a*c%p,b*c%p,c*c%p};
}
int reduced(int x,int p){x%=p;return x<0?x+p:x;}
int depth(const array<int,7>& sq,int p){
  auto power=sq;
  for(int j=2;j<=7;++j){
    int n=0;
    for(int i=0;i<7;++i) {power[i]=power[i]*sq[i]%p; n+=power[i];}
    if(n%p) return j;
  }
  assert(false);return -1;
}
int main(int argc,char**){
  bool low=argc>1;
  auto primes=low?vector<int>{17,19,23,31}:vector<int>{17,19,23,29,31};
  for(int p:primes){
    const int dim=low?3:8;
    vector<array<int,2>> V;
    vector<K> Q;
    for(int x=0;x<p;++x)for(int y=0;y<p;++y){
      array<int,2> v{x,y};
      if(v>array<int,2>{reduced(-x,p),reduced(-y,p)}) continue;
      V.push_back(v);Q.push_back(key(x,y,p));
    }
    const K tar{p-1,0,p-1,p-1,0,0,0,p-1};
    int N=V.size();
    auto tag=[p,dim](const K& k,K const& l){U u=0;for(int z=0;z<dim;++z)u=u*p+(k[z]+l[z])%p;return u;};
    unordered_multimap<U,array<int,2>> P;
    P.reserve(N*(N+1)/2);
    for(int i=0;i<N;++i)for(int j=i;j<N;++j)P.emplace(tag(Q[i],Q[j]),array<int,2>{i,j});
    long long count=0,nz=0,simple=0;
    int best=0,bestNZ=0,bestSimple=0;
    array<int,5> W{};
    const int e=find(V.begin(),V.end(),array<int,2>{1,0})-V.begin();
    const int f=find(V.begin(),V.end(),array<int,2>{0,1})-V.begin();
    for(int i=0;i<N;++i)for(int j=i;j<N;++j){
      K t;
      for(int u=0;u<dim;++u)t[u]=reduced(tar[u]-Q[i][u]-Q[j][u],p);
      for(int k=j;k<N;++k){
        U u=0;
        for(int r=0;r<dim;++r)u=u*p+(t[r]-Q[k][r]+p)%p;
        auto results=P.equal_range(u);
        for(auto it=results.first;it!=results.second;++it){
          auto [l,h]=it->second;
          if(l<k) continue;
          ++count;
          if(i) ++nz;
          bool isSimple=i>0 && i<j&&j<k&&k<l&&l<h&&
              i!=e&&j!=e&&k!=e&&l!=e&&h!=e&&i!=f&&j!=f&&k!=f&&l!=f&&h!=f;
          if(isSimple)++simple;
          int score=0;
          for(int t=0;t<=p;++t){
            array<int,7> sq{};
            array<int,7> inds={e,f,i,j,k,l,h};
            for(int r=0;r<7;++r){auto [x,y]=V[inds[r]];int a=t==p?y:(x+t*y)%p;sq[r]=a*a%p;}
            int d=depth(sq,p); assert(low||d>=3); score+=2*d;
          }
          best=max(best,score);
          if(i)bestNZ=max(bestNZ,score);
          if(isSimple&&score>bestSimple){bestSimple=score;W={i,j,k,l,h};}
        }
      }
    }
    int cap=p%14==1?7:6;
    cout<<"other bound "<<(low?2*(p+1+2*cap-2):4*(p+1+2*cap-4))<<" ";
    cout<<p<<" normalized total/nonzero/simple "<<count<<"/"<<nz<<"/"<<simple
        <<" max "<<best<<"/"<<bestNZ<<"/"<<bestSimple<<" simple witness basis +";
    if(bestSimple) for(int j:W) cout<<" ("<<V[j][0]<<","<<V[j][1]<<")";
    cout<<endl;
  }
}
