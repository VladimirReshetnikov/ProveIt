#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
using V=array<int,5>;
int p;
int m(long long x){int r=x%p;return r<0?r+p:r;}
int pw(int x,int j){int y=1;while(j){if(j&1)y=m(1LL*y*x);x=m(1LL*x*x);j/=2;}return y;}
V normalize(V v){int a=0; for(int x:v)if(x){a=x;break;}assert(a);int u=pw(a,p-2);for(int &x:v)x=m(1LL*x*u);return v;}
int moment(const V& v,int j){int s=0;for(int x:v)s+=pw(x,2*j);return m(s);}
V translate(const V& x,const V& y,int t){V v;for(int i=0;i<5;++i)v[i]=m(x[i]+1LL*t*y[i]);return v;}
void solve(int prime){
  p=prime;
  vector<int> squares,root(p,-1);
  for(int x=(p-1)/2;x>=0;--x)root[m(1LL*x*x)]=x;
  for(int k=0;k<p;++k)if(root[k]>=0)squares.push_back(k);
  const int half=(p+1)/2;
  set<V> reps;
  for(int a:squares)for(int b:squares){
    int s=m(-1-a-b),u=m(1LL*s*s+1+1LL*a*a+1LL*b*b);
    int e=m(1LL*half*u);
    if(m(1LL*s*s*s-3LL*s*e+1+1LL*a*a*a+1LL*b*b*b))continue;
    int w=root[m(1LL*s*s-4LL*e)];
    if(w<0)continue;
    int y=root[m(1LL*(s+w)*half)],z=root[m(1LL*(s-w)*half)];
    if(y<0||z<0)continue;
    V v{1,root[a],root[b],y,z};sort(v.begin(),v.end());reps.insert(v);
  }
  set<V> points;
  for(V v:reps)do{
    for(int j=0;j<32;++j){
      V w=v;for(int i=0;i<5;++i)if(j>>i&1)w[i]=m(-w[i]);
      points.insert(normalize(w));
    }
  }while(next_permutation(v.begin(),v.end()));
  for(auto w:points)for(int j=1;j<=3;++j)assert(moment(w,j)==0);
  int pairs=0,four=0,nonzero[5]={};
  for(auto x:reps)for(auto y:points){
    if(normalize(x)==y)continue;
    long long d=0;for(int i=0;i<5;++i)d+=1LL*x[i]*y[i];
    if(m(d))continue;
    ++pairs;
    // The pair spans an isotropic plane. Test the remaining p-1 rays.
    int num=2;
    for(int t=1;t<p;++t){
      V w=translate(x,y,t);
      if(!moment(w,2)&&!moment(w,3))++num;
    }
    if(num>=4)++four;
    bool nz=true;for(int i=0;i<5;++i)if(!x[i]&&!y[i])nz=false;
    if(nz){assert(num<=4);++nonzero[num];}
  }
  cout<<p<<" representatives "<<reps.size()<<" points "<<points.size()
      <<" incident pairs "<<pairs<<" four-depth>=4 pairs "<<four<<" nonzero pair counts (2,3,4) "<<nonzero[2]<<","<<nonzero[3]<<","<<nonzero[4]<<endl;
}
int main(){for(int p:{101,131,761,1031,1511,1571,2281,2351})solve(p);}
