// Exact integer certificate for the first-feedback response. Uses installed GMP.
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using Z=mpz_class;using Vec=std::vector<Z>;using Mat=std::vector<Vec>;
void require(bool p,const char*why){if(!p){std::cerr<<"FAILED: "<<why<<"\n";std::exit(1);}}
Z gcdz(const Z&a,const Z&b){Z v;mpz_gcd(v.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return v;}
Z lcmz(const Z&a,const Z&b){Z v;mpz_lcm(v.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return v;}
void normalize(Vec&v,Z&den){Z g=den;for(const Z&x:v)g=gcdz(g,x);if(den<0)g=-g;for(Z&x:v)mpz_divexact(x.get_mpz_t(),x.get_mpz_t(),g.get_mpz_t());mpz_divexact(den.get_mpz_t(),den.get_mpz_t(),g.get_mpz_t());}
Vec matvec(const Mat&A,const Vec&v){Vec out(A.size());for(size_t i=0;i<A.size();i++)for(size_t j=0;j<v.size();j++)if(A[i][j]!=0&&v[j]!=0)out[i]+=A[i][j]*v[j];return out;}
Z sum(const Vec&v){Z s=0;for(auto&x:v)s+=x;return s;}
struct RationalVector{Vec v;Z den;};
int main(int argc,char**argv){require(argc==3,"arguments m output.json");int m=std::stoi(argv[1]),d=2*m,n=d-1;auto started=std::chrono::steady_clock::now();Z D=Z(1)<<(d-1);std::vector<int>ix(n);for(int i=0;i<n;i++)ix[i]=i+1-m;
 Vec binom(d+1);for(int k=0;k<=d;k++)mpz_bin_uiui(binom[k].get_mpz_t(),d,k);
 Mat B(n,Vec(n)),C(n,Vec(n));for(int i=0;i<n;i++)for(int j=0;j<n;j++){int off=2*ix[i]-ix[j];if(std::abs(off)<=m)B[i][j]=binom[m+off];C[i][j]=(i==j?D:Z(0))-B[i][j];}C[0]=Vec(n,Z(1));
 // Fraction-free Gauss-Jordan on [C|I]. Every division is checked exact.
 Mat aug(n,Vec(2*n));for(int i=0;i<n;i++){for(int j=0;j<n;j++)aug[i][j]=C[i][j];aug[i][n+i]=1;}
 Z previous=1;
 for(int k=0;k<n;k++){
  int p=k;while(p<n&&aug[p][k]==0)p++;require(p<n,"nonzero pivot");if(p!=k)std::swap(aug[p],aug[k]);Z pivot=aug[k][k];
  for(int i=0;i<n;i++)if(i!=k){Z aik=aug[i][k];for(int j=0;j<2*n;j++)if(j!=k){Z t=aug[i][j]*pivot-aik*aug[k][j];require(mpz_divisible_p(t.get_mpz_t(),previous.get_mpz_t()),"fraction-free division");mpz_divexact(aug[i][j].get_mpz_t(),t.get_mpz_t(),previous.get_mpz_t());}aug[i][k]=0;}
  previous=pivot;
 }
 Z deninv=aug[0][0];Mat inv(n,Vec(n));for(int i=0;i<n;i++){require(aug[i][i]==deninv,"common inverse denominator");for(int j=0;j<n;j++){if(i!=j)require(aug[i][j]==0,"inverse diagonal");inv[i][j]=aug[i][n+j];}}
 // Eulerian atomic eigenvector, normalized exactly.
 Vec eul(1,Z(1));for(int r=2;r<=d-1;r++){Vec next(r);for(int k=0;k<r;k++){if(k<(int)eul.size())next[k]+=(k+1)*eul[k];if(k>0)next[k]+=(r-k)*eul[k-1];}eul=std::move(next);}
 Z fact;mpz_fac_ui(fact.get_mpz_t(),d-1);normalize(eul,fact);require(sum(eul)==fact,"atomic normalization");Vec b0=matvec(B,eul);for(int i=0;i<n;i++)require(b0[i]==D*eul[i],"atomic eigenvector");
 std::vector<RationalVector> hs;hs.push_back({eul,fact});Z Rnum=0;for(int i=0;i<n;i++)Rnum+=(std::abs(ix[i])%2?-eul[i]:eul[i]);Z Rden=fact;
 // Krawtchouk coefficients of (1-z)^(m+off)(1+z)^(m-off).
 Mat top(d+1,Vec(d+1));for(int off=-m;off<=m;off++){Vec K(d+1);K[0]=1;K[1]=-2*off;for(int k=1;k<d;k++){Z v=(-2*off)*K[k]-(d-k+1)*K[k-1];require(mpz_divisible_ui_p(v.get_mpz_t(),k+1),"Krawtchouk division");mpz_divexact_ui(K[k+1].get_mpz_t(),v.get_mpz_t(),k+1);}for(int k=0;k<=d;k++)top[m+off][k]=binom[m+off]*K[k];}
 for(int order=1;order<=d;order++){
  Z common=1;for(auto&h:hs)common=lcmz(common,h.den);if(order==d)common=lcmz(common,Rden*fact);Vec rhs(n);
  for(int j=1;j<=order;j++){auto&h=hs[order-j];Z scale=common/h.den;for(int i=0;i<n;i++){Z dot=0;for(int k=0;k<n;k++){int off=2*ix[i]-ix[k];if(std::abs(off)<=m&&h.v[k]!=0)dot+=top[m+off][j]*h.v[k];}rhs[i]+=dot*scale;}}
  if(order==d){Z scale=D*Rnum*(common/(Rden*fact));if(m%2)scale=-scale;for(int i=0;i<n;i++)rhs[i]-=scale*eul[i];}
  require(sum(rhs)==0,"right hand side normalization");Vec target=rhs;rhs[0]=0;Vec hn=matvec(inv,rhs);Z den=deninv*common;normalize(hn,den);require(sum(hn)==0,"response normalization");Vec bh=matvec(B,hn);for(int i=0;i<n;i++)require((D*hn[i]-bh[i])*common==target[i]*den,"exact linear residual");hs.push_back({std::move(hn),std::move(den)});
 }
 auto&last=hs.back();Z num=0;for(int i=0;i<n;i++)num+=(std::abs(ix[i])%2?-last.v[i]:last.v[i]);if(m%2)num=-num;Z den=last.den,g=gcdz(num,den);num/=g;den/=g;require(num>0,"positive boundary response");double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
 std::ofstream out(argv[2]);out<<"{\n  \"m\": "<<m<<",\n  \"all_checks_passed\": true,\n  \"exact_linear_residuals\": "<<d<<",\n  \"H_boundary_numerator\": \""<<num<<"\",\n  \"H_boundary_denominator\": \""<<den<<"\",\n  \"elapsed_seconds\": "<<seconds<<",\n  \"method\": \"GMP exact integers, checked fraction-free inverse, shared-denominator vectors, exact residuals at every order\"\n}\n";
 std::cout<<"m "<<m<<" positive; "<<d<<" exact residuals; "<<seconds<<" seconds; "<<num.get_str().size()<<" numerator digits\n";
}
