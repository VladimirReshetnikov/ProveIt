// Exact modular proof certificate for every 7 <= b < 11520 at a=6.
// Every arithmetic operation is in F_65537; there are no floating point values.
// Compile: c++ -O2 -std=c++17 complete_p12.cpp -o complete_p12
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using I=std::int64_t;
constexpr I P=65537;
constexpr int a=6, limit=11520;
I mod(I x){x%=P;return x<0?x+P:x;}
I mul(I x,I y){return mod(x*y);}
I power(I x,I n){I r=1;for(;n;n>>=1,x=mul(x,x))if(n&1)r=mul(r,x);return r;}
std::vector<I> fac(4*limit+5),fi(fac.size()),in(fac.size()),B(2*limit);
I falling(I x,int k){I r=1;for(int j=0;j<k;++j)r=mul(r,x-j);return r;}
I choose(int n,int k){return (k<0||k>n)?0:mul(fac[n],mul(fi[k],fi[n-k]));}
I determinant(std::vector<std::vector<I>> A){
 I ans=1;
 for(int k=0;k<int(A.size());++k){
  int r=k;while(r<int(A.size())&&!A[r][k])++r;
  if(r==int(A.size()))return 0;
  if(r!=k){std::swap(A[r],A[k]);ans=mod(-ans);}
  I z=A[k][k];ans=mul(ans,z);I zi=power(z,P-2);
  for(r=k+1;r<int(A.size());++r){
   I u=mul(A[r][k],zi);
   for(int c=k;c<int(A.size());++c)A[r][c]=mod(A[r][c]-mul(u,A[k][c]));
  }
 }
 return ans;
}
std::vector<std::vector<I>> retained(int b){
 std::vector<std::vector<I>> A(a,std::vector<I>(a));
 for(int i=0;i<a;++i){
  int n=b-a+i;std::vector<I>d(2*i+2);
  for(int h=1;h<=2*i+1;h+=2){
   I sum=0;
   for(int j=0;j<=h;++j){
    I W=mul(2*n+2-j,falling(4*n+2-j,2*i));
    sum=mod(sum+((h-j)%2?-1:1)*mul(choose(h,j),W));
   }
   d[h]=mul(sum,fi[h]);
  }
  for(int l=0;l<a;++l){
   int N=2*(n-l)+1,R=2*b-2*a+2+2*l;
   I F=mul(mul(falling(2*n,2*l),falling(2*n+2*l+2,2*l)),fi[2*l+1]);
   I scale=mul(mul(fac[R],fi[N]),mul(mul(in[2*n+1],in[2*n+2]),fi[2*l+2]));
   I sum=0;
   for(int k=0;k<=i;++k){
    int ix=2*b-2*(a-i+l+k);
    assert(ix>=2&&ix<int(B.size()));
    sum=mod(sum+mul(mul(d[2*k+1],falling(N,2*k+1)),2*B[ix]));
   }
   A[i][l]=mod(2*F+mul(scale,sum));
  }
 }
 return A;
}
std::vector<std::vector<I>> original(int b){
 std::vector<std::vector<I>> M(b,std::vector<I>(b));
 for(int i=0;i<b;++i)for(int k=0;k<b;++k){
  int e=2*(i+k-a+1);if(e<0)continue;
  I v=0;
  int U=2*i+2,L=2*a-2*k;
  if(L>=2&&L<=U)v=mul(choose(U,L),in[U]);
  U=2*b+2*i-2*a+2;L=2*b-2*k;
  if(L>=2&&L<=U)v=mod(v+mul(choose(U,L),in[U]));
  M[i][k]=mul(B[e],v);
 }
 return M;
}
I multiplier(int b){
 I ans=((a*(b-a)+a*(a-1)/2)%2)?P-1:1;
 for(int t=0;t<b;++t)ans=mul(ans,mul(fac[2*b+2*t-2*a+1],fi[2*b-2*t]));
 for(int n=0;n<b-a;++n)ans=mul(ans,mul(mul(fac[2*n+1],fac[2*n+1]),mul(fi[4*n+2],fi[4*n+3])));
 for(int i=0;i<a;++i){int n=b-a+i;ans=mul(ans,mul(2*n+1,mul(fac[2*n+2],fi[4*n+2])));}
 return ans;
}
int main(int argc,char**argv){
 for(I d=2;d*d<=P;++d)assert(P%d);
 assert(4*limit+5<P);
 fac[0]=1;for(int j=1;j<int(fac.size());++j)fac[j]=mul(fac[j-1],j);
 fi.back()=power(fac.back(),P-2);
 for(int j=int(fi.size())-1;j>0;--j)fi[j-1]=mul(fi[j],j);
 for(int j=1;j<int(in.size());++j)in[j]=mul(fac[j-1],fi[j]);
 B[0]=1;B[1]=mod(-in[2]);
 for(int n=2;n<int(B.size());n+=2){
  I bin=1,s=mod(1-mul(n+1,in[2]));
  for(int k=2;k<n;k+=2){
   bin=mul(bin,mul(mul(n+3-k,n+2-k),mul(in[k],in[k-1])));
   s=mod(s+mul(bin,B[k]));
  }
  B[n]=mod(-mul(s,in[n+1]));
 }
 std::vector<int> zeros;
 std::vector<I> vals;
 for(int b=a+1;b<limit;++b){
  I v=determinant(b<2*a?original(b):retained(b));
  vals.push_back(v);if(!v)zeros.push_back(b);
  if(b>=2*a&&b<=32)assert(determinant(original(b))==mul(v,multiplier(b)));
 }
 std::ofstream out(argc>1?argv[1]:"complete_p12.json");
 out<<"{\n  \"a\": "<<a<<",\n  \"prime\": "<<P<<",\n  \"b_start\": "<<a+1
 <<",\n  \"b_end_inclusive\": "<<limit-1<<",\n  \"case_count\": "<<vals.size()
 <<",\n  \"direct_source_small_cases\": 5,\n  \"normalization_overlap_checks\": 21,\n  \"zero_residue_cases\": [";
 for(size_t j=0;j<zeros.size();++j)out<<(j?", ":"")<<zeros[j];
 out<<"],\n  \"determinant_residues\": [\n    ";
 for(size_t j=0;j<vals.size();++j){out<<(j?", ":"")<<vals[j];if(j%20==19)out<<"\n    ";}
 out<<"\n  ],\n  \"all_checks_passed\": "<<(zeros.empty()?"true":"false")<<"\n}\n";
 std::cout<<"Cases: "<<vals.size()<<"; zero residue cases:";
 for(int z:zeros)std::cout<<" "<<z;
 std::cout<<"\n";
 return zeros.empty()?0:2;
}
