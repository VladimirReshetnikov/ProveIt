// Exact fixed-grid sign certificate using reflection blocks; only GMP integers.
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using Z=mpz_class;using Vec=std::vector<Z>;using Mat=std::vector<Vec>;
void req(bool p,const char*s){if(!p){std::cerr<<"FAILED "<<s<<"\n";std::exit(1);}}
struct Inverse{Mat N;Z den,alpha;Z alphaDen;};
Inverse invert(Mat A,bool even){int n=A.size();Mat g(n,Vec(2*n));for(int i=0;i<n;i++){for(int j=0;j<n;j++)g[i][j]=A[i][j];g[i][n+i]=1;}Z prev=1;
 for(int k=0;k<n;k++){int p=k;while(p<n&&g[p][k]==0)p++;req(p<n,"pivot");if(p!=k)std::swap(g[p],g[k]);Z pivot=g[k][k];for(int i=0;i<n;i++)if(i!=k){Z x=g[i][k];for(int j=0;j<2*n;j++)if(j!=k){Z t=g[i][j]*pivot-x*g[k][j];req(mpz_divisible_p(t.get_mpz_t(),prev.get_mpz_t()),"exact Bareiss division");mpz_divexact(g[i][j].get_mpz_t(),t.get_mpz_t(),prev.get_mpz_t());}g[i][k]=0;}prev=pivot;}
 Z den=g[0][0];Mat N(n,Vec(n));for(int i=0;i<n;i++)for(int j=0;j<n;j++)N[i][j]=g[i][n+j];if(den<0){den=-den;for(auto&row:N)for(auto&x:row)x=-x;}
 for(int i=0;i<n;i++)for(int j=0;j<n;j++){Z v=0;for(int k=0;k<n;k++)v+=A[i][k]*N[k][j];req(v==(i==j?den:Z(0)),"inverse identity");}
 Z alpha=0;for(int j=(even?1:0);j<n;j++){Z col=0;for(int i=0;i<n;i++)col+=(even?(i==0?1:2):1)*abs(N[i][j]);if(col>alpha)alpha=col;}
 return{std::move(N),den,alpha,even?2*den:den};}
Vec product(const Mat&A,const Vec&v){Vec o(A.size());for(size_t i=0;i<A.size();i++)for(size_t j=0;j<v.size();j++)o[i]+=A[i][j]*v[j];return o;}
int main(int argc,char**argv){req(argc==3,"m output.json");int m=std::stoi(argv[1]),d=2*m;auto begin=std::chrono::steady_clock::now();Z D=Z(1)<<(d-1);Vec choose(d+1);for(int k=0;k<=d;k++)mpz_bin_uiui(choose[k].get_mpz_t(),d,k);
 auto b0=[&](int k,int r)->Z{int off=2*k-r;return std::abs(off)<=m?choose[m+off]:Z(0);};
 Mat Ce(m,Vec(m)),Co(m-1,Vec(m-1));for(int k=0;k<m;k++)for(int r=0;r<m;r++)Ce[k][r]=(k==r?D:Z(0))-b0(k,r)-(r>0?b0(k,-r):Z(0));for(int r=0;r<m;r++)Ce[0][r]=(r==0?1:2);
 for(int k=1;k<m;k++)for(int r=1;r<m;r++)Co[k-1][r-1]=(k==r?D:Z(0))-b0(k,r)+b0(k,-r);
 Inverse even=invert(Ce,true),odd=invert(Co,false);
 Vec e(1,Z(1));for(int r=2;r<=d-1;r++){Vec ne(r);for(int k=0;k<r;k++){if(k<(int)e.size())ne[k]+=(k+1)*e[k];if(k>0)ne[k]+=(r-k)*e[k-1];}e=std::move(ne);}Z fact;mpz_fac_ui(fact.get_mpz_t(),d-1);Z common=fact;for(auto&x:e)mpz_gcd(common.get_mpz_t(),common.get_mpz_t(),x.get_mpz_t());for(auto&x:e)x/=common;fact/=common;
 Vec h0(m);for(int k=0;k<m;k++)h0[k]=e[m-1+k];Z norm=h0[0];for(int k=1;k<m;k++)norm+=2*h0[k];req(norm==fact,"Eulerian normalization");for(int k=0;k<m;k++){Z v=b0(k,0)*h0[0];for(int r=1;r<m;r++)v+=(b0(k,r)+b0(k,-r))*h0[r];req(v==D*h0[k],"atomic eigenvector");}
 Z Rnum=h0[0];for(int k=1;k<m;k++)Rnum+=(k%2?-2*h0[k]:2*h0[k]);
 Mat top(d+1,Vec(d+1));for(int off=-m;off<=m;off++){Vec K(d+1);K[0]=1;K[1]=-2*off;for(int j=1;j<d;j++){Z v=(-2*off)*K[j]-(d-j+1)*K[j-1];req(mpz_divisible_ui_p(v.get_mpz_t(),j+1),"Krawtchouk division");mpz_divexact_ui(K[j+1].get_mpz_t(),v.get_mpz_t(),j+1);}for(int j=0;j<=d;j++)top[m+off][j]=choose[m+off]*K[j];}
 auto bj=[&](int j,int k,int r)->Z{int off=2*k-r;return std::abs(off)<=m?top[m+off][j]:Z(0);};
 const int precision=256;Z scale=(Z(1)<<precision)*fact*fact;std::vector<Vec>hs(1,Vec(m));for(int k=0;k<m;k++)hs[0][k]=h0[k]*(scale/fact);Vec error(1,Z(0));
 std::ofstream trace(std::string(argv[2])+".trace");trace<<"TMP1 "<<m<<" "<<d<<" "<<precision<<"\n"<<scale<<"\n"<<even.alpha<<" "<<even.alphaDen<<"\n"<<odd.alpha<<" "<<odd.alphaDen<<"\n";for(auto&v:hs[0])trace<<v<<" ";trace<<0<<"\n";
 for(int order=1;order<=d;order++){bool iseven=order%2==0;int start=iseven?0:1,n=m-start;Vec rhs(n);for(int j=1;j<=order;j++){bool inputEven=(order-j)%2==0;int rstart=inputEven?0:1;for(int k=start;k<m;k++)for(int r=rstart;r<m;r++){Z coeff=bj(j,k,r);if(r>0)coeff+=(inputEven?bj(j,k,-r):-bj(j,k,-r));rhs[k-start]+=coeff*hs[order-j][r-rstart];}}
  if(order==d){Z f=D*Rnum*(scale/(fact*fact));if(m%2)f=-f;for(int k=0;k<m;k++)rhs[k]-=f*h0[k];}if(iseven)rhs[0]=0;
  auto&iv=iseven?even:odd;Vec v=product(iv.N,rhs),hn(n);for(int k=0;k<n;k++){mpz_fdiv_q(hn[k].get_mpz_t(),v[k].get_mpz_t(),iv.den.get_mpz_t());req(hn[k]*iv.den<=v[k]&&v[k]<(hn[k]+1)*iv.den,"grid rounding");}
  Z e=0;for(int j=1;j<=order;j++)e+=choose[j]*error[order-j];e*=iv.alpha*D;Z rad;mpz_cdiv_q(rad.get_mpz_t(),e.get_mpz_t(),iv.alphaDen.get_mpz_t());int round=iseven?d-1:d-2;rad+=round;req((rad-round)*iv.alphaDen>=e,"error rounding");for(auto&x:hn)trace<<x<<" ";trace<<rad<<"\n";hs.push_back(std::move(hn));error.push_back(std::move(rad));
 }
 Z midpoint=hs[d][0];for(int k=1;k<m;k++)midpoint+=(k%2?-2*hs[d][k]:2*hs[d][k]);if(m%2)midpoint=-midpoint;Z lower=midpoint-error[d],upper=midpoint+error[d];req(lower>0,"positive lower endpoint");double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();std::ofstream out(argv[2]);out<<"{\n  \"m\": "<<m<<",\n  \"all_checks_passed\": true,\n  \"precision_bits\": "<<precision<<",\n  \"checked_response_orders\": "<<d<<",\n  \"H_lower_numerator\": \""<<lower<<"\",\n  \"H_upper_numerator\": \""<<upper<<"\",\n  \"common_denominator\": \""<<scale<<"\",\n  \"error_radius_numerator\": \""<<error[d]<<"\",\n  \"elapsed_seconds\": "<<seconds<<",\n  \"method\": \"Exact GMP integer enclosures in reflection blocks, verified inverse identities, weighted-l1 error propagation and outward rounding\"\n}\n";std::cout<<"m "<<m<<" positive parity interval; "<<seconds<<" seconds; margin bits "<<(mpz_sizeinbase(midpoint.get_mpz_t(),2)-mpz_sizeinbase(error[d].get_mpz_t(),2))<<"\n";
}
