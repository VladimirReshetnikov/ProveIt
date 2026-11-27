#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
using namespace std;
using V=array<int,6>;
V F[63][6],G[63][6];
int poly[6], ell[6];
V mul(V a,V b){
  int t[11]={};
  for(int i=0;i<6;i++)for(int j=0;j<6;j++)t[i+j]+=a[i]*b[j];
  for(int j=10;j>=6;j--)for(int i=0;i<6;i++)t[j-6+i]-=(t[j]&15)*poly[i];
  V v;
  for(int i=0;i<6;i++)v[i]=t[i]&15;
  return v;
}
int ord(int x){return x?__builtin_ctz((unsigned)x):4;}
bool full15(int a[6][6]){
  for(int k=0;k<6;k++){
    int vi=k,vj=k,r=4;
    for(int i=k;i<6;i++)for(int j=k;j<6;j++){
      int h=ord(a[i][j]);
      if(h<r){vi=i;vj=j;r=h;}
      if(r==0)break;
    }
    if(r==4)return false;
    for(int i=0;i<6;i++)swap(a[i][k],a[i][vj]);
    for(int j=0;j<6;j++)swap(a[k][j],a[vi][j]);
    int unit=a[k][k]>>r;
    int inv=unit;
    for(int i=k+1;i<6;i++){
      int c=(a[i][k]>>r)*inv; // any odd unit is self-inverse mod 8, but not mod16
      if(r==0) c=(a[i][k])*unit*(2-unit*unit);
      for(int j=k+1;j<6;j++)a[i][j]=(a[i][j]-c*a[k][j])&15;
      a[i][k]=0;
    }
  }
  return true;
}

// Independent replay: work a bit at a time. If the remaining block
// is even, divide by two and lose one bit of available precision.
bool check_bits(int a[6][6]){
  int mask=15;
  for(int k=0;k<6;k++){
    int pi=-1,pj=-1;
    while(pi<0){
      for(int i=k;i<6&&pi<0;i++)for(int j=k;j<6;j++)
        if(a[i][j]&1){pi=i;pj=j;break;}
      if(pi>=0)break;
      mask>>=1;
      if(!mask)return false;
      for(int i=k;i<6;i++)for(int j=k;j<6;j++)a[i][j]>>=1;
    }
    for(int i=k;i<6;i++)swap(a[i][k],a[i][pj]);
    for(int j=k;j<6;j++)swap(a[k][j],a[pi][j]);
    int u=a[k][k],inv=u*(2-u*u);
    for(int i=k+1;i<6;i++){
      int c=a[i][k]*inv;
      for(int j=k+1;j<6;j++)a[i][j]=(a[i][j]-c*a[k][j])&mask;
      a[i][k]=0;
    }
  }
  return true;
}
uint64_t n=0, yes=0, old=0, count[7]={}, certified[7]={};
int A[6],J[6];
bool gf2(){
  int basis[6]={};
  for(int j=0;j<6;j++){
    int v=0;
    for(int i=0;i<6;i++)v|=(G[A[j]][J[j]][i]&1)<<i;
    for(int i=5;i>=0;i--)if(v>>i&1) {
      if(!basis[i]){basis[i]=v;break;}
      v^=basis[i];
    }
    if(!v)return false;
  }
  return true;
}
void rec(int k,int r,int j,int blocks){
  if(k==6){
    ++n;++count[blocks];
    int m[6][6], m2[6][6];
    for(int i=0;i<6;i++)for(int j=0;j<6;j++)m2[i][j]=m[i][j]=F[A[j]][J[j]][i];
    bool pass=full15(m), before=gf2();
    assert(pass==check_bits(m2));
    assert(!before||pass);
    if(before)++old;
    if(pass){++yes;++certified[blocks];}
    return;
  }
  for(int a=r;a<63;a++){
    A[k]=a;J[k]=a==r?j+1:0;
    rec(k+1,a,J[k],blocks+(r!=a));
  }
}
int main(){
  for(int& v:poly)cin>>v;
  for(int& v:ell)cin>>v;
  V x{1,0,0,0,0,0}, z{0,1,0,0,0,0}, d;
  for(int i=0;i<6;i++)d[i]=ell[i];
  const int s[6]={4,3,4,2,4,3};
  for(int a=0;a<63;a++,x=mul(x,z)){
    V w=x;
    for(int j=0;j<6;j++,w=mul(w,d)){
      G[a][j]=w;
      for(int i=0;i<6;i++)F[a][j][i]=(w[i]<<(4-s[j]))&15;
    }
  }
  rec(1,0,0,1);
  cout<<"Old "<<old<<" improved "<<yes<<" total "<<n<<"\n";
  assert(old==3892897&&n==9657648&&yes==8574847);
  for(int j=1;j<=6;j++)cout<<j<<" "<<certified[j]<<" "<<count[j]<<"\n";
}
