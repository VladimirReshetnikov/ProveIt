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
 Z Rnum=0;for(int i=0;i<n;i++)Rnum+=(std::abs(ix[i])%2?-eul[i]:eul[i]);Z Rden=fact;
 // Krawtchouk coefficients of (1-z)^(m+off)(1+z)^(m-off).
 Mat top(d+1,Vec(d+1));for(int off=-m;off<=m;off++){Vec K(d+1);K[0]=1;K[1]=-2*off;for(int k=1;k<d;k++){Z v=(-2*off)*K[k]-(d-k+1)*K[k-1];require(mpz_divisible_ui_p(v.get_mpz_t(),k+1),"Krawtchouk division");mpz_divexact_ui(K[k+1].get_mpz_t(),v.get_mpz_t(),k+1);}for(int k=0;k<=d;k++)top[m+off][k]=binom[m+off]*K[k];}
 // Certify the computed inverse and its restricted column norm exactly.
 if(deninv<0){deninv=-deninv;for(auto&row:inv)for(auto&x:row)x=-x;}
 for(int i=0;i<n;i++)for(int j=0;j<n;j++){Z v=0;for(int k=0;k<n;k++)v+=C[i][k]*inv[k][j];require(v==(i==j?deninv:Z(0)),"exact inverse identity");}
 Z alpha=0;for(int j=1;j<n;j++){Z col=0;for(int i=0;i<n;i++)col+=abs(inv[i][j]);if(col>alpha)alpha=col;}
 const int precision=256;Z scale=(Z(1)<<precision)*fact*fact;
 std::vector<Vec> hs(1,Vec(n));for(int i=0;i<n;i++)hs[0][i]=eul[i]*(scale/fact);
 Vec errors(1,Z(0));
 std::ofstream trace(std::string(argv[2])+".trace");
 trace<<"TMM1 "<<m<<" "<<d<<" "<<n<<" "<<precision<<"\n"<<scale<<"\n"<<alpha<<" "<<deninv<<"\n";
 for(const auto&v:hs[0])trace<<v<<" ";trace<<0<<"\n";
 for(int order=1;order<=d;order++){
  Vec rhs(n);
  for(int j=1;j<=order;j++)for(int i=0;i<n;i++)for(int k=0;k<n;k++){int off=2*ix[i]-ix[k];if(std::abs(off)<=m&&hs[order-j][k]!=0)rhs[i]+=top[m+off][j]*hs[order-j][k];}
  if(order==d){Z f=D*Rnum*(scale/(Rden*fact));if(m%2)f=-f;for(int i=0;i<n;i++)rhs[i]-=f*eul[i];}
  rhs[0]=0;Vec product=matvec(inv,rhs),hn(n);
  for(int i=0;i<n;i++){mpz_fdiv_q(hn[i].get_mpz_t(),product[i].get_mpz_t(),deninv.get_mpz_t());require(hn[i]*deninv<=product[i]&&product[i]<(hn[i]+1)*deninv,"checked fixed-grid rounding");}
  Z bound=0;for(int j=1;j<=order;j++)bound+=binom[j]*errors[order-j];bound*=alpha*D;
  Z radius;mpz_cdiv_q(radius.get_mpz_t(),bound.get_mpz_t(),deninv.get_mpz_t());radius+=n;
  require((radius-n)*deninv>=bound,"outward error rounding");
  for(const auto&v:hn)trace<<v<<" ";trace<<radius<<"\n";
  hs.push_back(std::move(hn));errors.push_back(std::move(radius));
 }
 Z midpoint=0;for(int i=0;i<n;i++)midpoint+=(std::abs(ix[i])%2?-hs[d][i]:hs[d][i]);if(m%2)midpoint=-midpoint;
 Z lower=midpoint-errors[d],upper=midpoint+errors[d];require(lower>0,"strict positive rational lower endpoint");
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
 std::ofstream out(argv[2]);out<<"{\n  \"m\": "<<m<<",\n  \"all_checks_passed\": true,\n  \"precision_bits\": "<<precision<<",\n  \"checked_response_orders\": "<<d<<",\n  \"H_lower_numerator\": \""<<lower<<"\",\n  \"H_upper_numerator\": \""<<upper<<"\",\n  \"common_denominator\": \""<<scale<<"\",\n  \"error_radius_numerator\": \""<<errors[d]<<"\",\n  \"inverse_norm_numerator\": \""<<alpha<<"\",\n  \"inverse_norm_denominator\": \""<<deninv<<"\",\n  \"elapsed_seconds\": "<<seconds<<",\n  \"method\": \"Exact integer fixed-grid enclosures, certified inverse identity, rigorous induced-norm error recurrence, outward integer rounding\"\n}\n";
 std::cout<<"m "<<m<<" positive interval; "<<d<<" exact enclosure steps; "<<seconds<<" seconds; margin bits "<<(mpz_sizeinbase(midpoint.get_mpz_t(),2)-mpz_sizeinbase(errors[d].get_mpz_t(),2))<<"\n";
}
