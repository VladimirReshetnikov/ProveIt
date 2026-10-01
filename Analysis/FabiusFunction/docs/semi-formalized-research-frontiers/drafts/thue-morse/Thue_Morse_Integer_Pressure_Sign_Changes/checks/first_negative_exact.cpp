// Exact normalized eigenvalue and pressure recursion using a row-polynomial gauge.
// The gauge is similar to V_a, but each Taylor matrix is diag(K_j(k))*A.
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using Z=mpz_class;using Q=mpq_class;using Vec=std::vector<Z>;using Mat=std::vector<Vec>;
Q rat(long n,long d){Q q(n,d);q.canonicalize();return q;}
void req(bool p,const char*w){if(!p){std::cerr<<"FAIL "<<w<<"\n";exit(1);}}
Z gz(const Z&a,const Z&b){Z z;mpz_gcd(z.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return z;}
Z lz(const Z&a,const Z&b){Z z;mpz_lcm(z.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return z;}
void norm(Vec&v,Z&den){Z g=den;for(auto&x:v)g=gz(g,x);if(den<0)g=-g;for(auto&x:v)x/=g;den/=g;}
Vec mv(const Mat&A,const Vec&v){Vec z(A.size());for(size_t i=0;i<A.size();i++)for(size_t j=0;j<v.size();j++)if(A[i][j]!=0&&v[j]!=0)z[i]+=A[i][j]*v[j];return z;}
Z sum(const Vec&v){Z z=0;for(auto&x:v)z+=x;return z;}
struct RV{Vec v;Z den;};
Z weighted_sum(const Vec&v){Z z=v[0];for(size_t i=1;i<v.size();i++)z+=2*v[i];return z;}
struct Inverse{Mat matrix;Z den;};
Inverse inverse(const Mat&C){int n=C.size();Mat aug(n,Vec(2*n));for(int i=0;i<n;i++)for(int j=0;j<n;j++){aug[i][j]=C[i][j];aug[i][n+j]=(i==j);}Z previous=1;
 for(int k=0;k<n;k++){int p=k;while(p<n&&aug[p][k]==0)p++;req(p<n,"pivot");if(p!=k)std::swap(aug[p],aug[k]);Z pivot=aug[k][k];for(int i=0;i<n;i++)if(i!=k){Z aik=aug[i][k];for(int j=0;j<2*n;j++)if(j!=k){Z z=aug[i][j]*pivot-aik*aug[k][j];req(mpz_divisible_p(z.get_mpz_t(),previous.get_mpz_t()),"Bareiss exact");mpz_divexact(aug[i][j].get_mpz_t(),z.get_mpz_t(),previous.get_mpz_t());}aug[i][k]=0;}previous=pivot;}
 Z den=aug[0][0];Mat inv(n,Vec(n));for(int i=0;i<n;i++){req(aug[i][i]==den,"inverse diagonal");for(int j=0;j<n;j++){if(i!=j)req(aug[i][j]==0,"inverse offdiag");inv[i][j]=aug[i][n+j];}}return {inv,den};}

std::vector<Q> mul(const std::vector<Q>&a,const std::vector<Q>&b,int N){std::vector<Q>z(N+1);for(int i=0;i<(int)a.size()&&i<=N;i++)if(a[i]!=0)for(int j=0;j<(int)b.size()&&i+j<=N;j++)if(b[j]!=0)z[i+j]+=a[i]*b[j];return z;}
int main(int argc,char**argv){req(argc==4,"usage m maximum_even_index output.json");int m=std::stoi(argv[1]),limit=std::stoi(argv[2]),d=2*m,n=d-1,top=2*limit;req(m>=2 && limit>=3*m,"domain");auto start=std::chrono::steady_clock::now();Z D=Z(1)<<(d-1);Vec bin(d+1);for(int j=0;j<=d;j++)mpz_bin_uiui(bin[j].get_mpz_t(),d,j);
 n=m;std::vector<int>ix(n);for(int i=0;i<n;i++)ix[i]=i;
 Mat Be(n,Vec(n)),Bo(n,Vec(n));auto entry=[&](int k,int r)->Z{int p=m+2*k-r;return 0<=p&&p<=d?bin[p]:Z(0);};
 for(int k=0;k<n;k++)for(int r=0;r<n;r++){Be[k][r]=entry(k,r)+(r?entry(k,-r):Z(0));if(r)Bo[k][r]=entry(k,r)-entry(k,-r);}
 Mat Ce(n,Vec(n)),Co(n-1,Vec(n-1));for(int i=0;i<n;i++)for(int j=0;j<n;j++)Ce[i][j]=(i==j?D:Z(0))-Be[i][j];for(int j=0;j<n;j++)Ce[0][j]=(j?2:1);for(int i=1;i<n;i++)for(int j=1;j<n;j++)Co[i-1][j-1]=(i==j?D:Z(0))-Bo[i][j];
 Inverse ie=inverse(Ce),io=inverse(Co);
 Vec full(1,Z(1));for(int r=2;r<=d-1;r++){Vec v(r);for(int k=0;k<r;k++){if(k<(int)full.size())v[k]+=(k+1)*full[k];if(k)v[k]+=(r-k)*full[k-1];}full=std::move(v);}Vec eul(n);for(int k=0;k<n;k++)eul[k]=full[m-1+k];Z fact;mpz_fac_ui(fact.get_mpz_t(),d-1);norm(eul,fact);req(weighted_sum(eul)==fact,"h0 sum");Vec y0=mv(Be,eul);for(int i=0;i<n;i++)req(y0[i]==D*eul[i],"h0 residual");Z yd=fact;norm(y0,yd);
 Mat K(d+1,Vec(n));for(int i=0;i<n;i++){K[0][i]=1;K[1][i]=-2*ix[i];for(int j=1;j<d;j++){Z z=(-2*ix[i])*K[j][i]-(d-j+1)*K[j-1][i];req(mpz_divisible_ui_p(z.get_mpz_t(),j+1),"Krawtchouk exact");mpz_divexact_ui(K[j+1][i].get_mpz_t(),z.get_mpz_t(),j+1);}}
 std::vector<RV> hs{{eul,fact}}, ys{{y0,yd}};std::vector<Q>lam(top+1);lam[0]=1;size_t maxdigits=0;
 for(int order=1;order<=top;order++){
  Z common=1;for(int j=1;j<=std::min(order,d);j++)common=lz(common,ys[order-j].den);
  for(int j=1;j<order;j++)if(lam[j]!=0)common=lz(common,lam[j].get_den()*hs[order-j].den);
  Vec rhs(n);
  for(int j=1;j<=std::min(order,d);j++){auto&y=ys[order-j];Z scale=common/y.den;for(int i=0;i<n;i++)if(K[j][i]!=0&&y.v[i]!=0)rhs[i]+=K[j][i]*y.v[i]*scale;}
  lam[order]=(order%2?Q(0):Q(weighted_sum(rhs),D*common));lam[order].canonicalize();if(order%2)req(rhs[0]==0,"odd zero coordinate");
  if(order<d||order%2)req(lam[order]==0,"vanishing eigenvalue coefficient");
  for(int j=1;j<order;j++)if(lam[j]!=0){auto&h=hs[order-j];Z scale=D*lam[j].get_num()*(common/(lam[j].get_den()*h.den));for(int i=0;i<n;i++)rhs[i]-=scale*h.v[i];}
  if(lam[order]!=0){Z c2=lz(common,lam[order].get_den()*fact);Z scale=c2/common;for(auto&x:rhs)x*=scale;common=c2;scale=D*lam[order].get_num()*(common/(lam[order].get_den()*fact));for(int i=0;i<n;i++)rhs[i]-=scale*eul[i];}
  if(order%2)req(rhs[0]==0,"odd rhs normalization");else req(weighted_sum(rhs)==0,"even rhs normalization");Vec target=rhs;Vec hn;Z den;
  if(order%2){Vec rr(rhs.begin()+1,rhs.end());auto z=mv(io.matrix,rr);hn.push_back(0);hn.insert(hn.end(),z.begin(),z.end());den=io.den*common;}else{rhs[0]=0;hn=mv(ie.matrix,rhs);den=ie.den*common;}
  norm(hn,den);if(order%2)req(hn[0]==0,"odd h normalization");else req(weighted_sum(hn)==0,"even h normalization");
  Vec bh=mv(order%2?Bo:Be,hn);for(int i=0;i<n;i++)req((D*hn[i]-bh[i])*common==target[i]*den,"original Fourier residual on parity block");
  hs.push_back({hn,den});Z bden=den;norm(bh,bden);ys.push_back({std::move(bh),std::move(bden)});maxdigits=std::max(maxdigits,den.get_str().size());
  if(order%20==0){double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cerr<<"m "<<m<<" order "<<order<<" / "<<top<<" secs "<<sec<<" den digits "<<den.get_str().size()<<"\n";}
 }
 // Full formal logarithm in x=a^2, with all feedback orders retained.
 std::vector<Q>L(limit+1),logL(limit+1);L[0]=1;for(int j=1;j<=limit;j++)L[j]=(j%2?-lam[2*j]:lam[2*j]);
 for(int j=1;j<=limit;j++){logL[j]=L[j];for(int i=1;i<j;i++)logL[j]-=rat(i,j)*logL[i]*L[j-i];}
 // T(x)=tan(sqrt(x))/sqrt(x), by y'=1+y².
 std::vector<Q>tanT(limit+1);tanT[0]=1;for(int j=1;j<=limit;j++){Q q=0;for(int k=0;k<j;k++)q+=tanT[k]*tanT[j-1-k];tanT[j]=q/(2*j+1);}
 auto T2=mul(tanT,tanT,limit);std::vector<Q>power(limit+1);power[0]=1;std::vector<Q>pressure(limit+1);
 for(int j=1;j<=limit;j++){power=mul(power,T2,limit);if(logL[j]!=0)for(int k=j;k<=limit;k++)pressure[k]+=logL[j]*power[k-j];}
 for(int k=1;k<=limit;k++)pressure[k]-=rat(m,k)*tanT[k-1];
 req(pressure[m]==0,"missing pressure coefficient");for(int k=m+1;k<3*m;k++)req(pressure[k]>0,"known positive window");int first_negative=0;for(int k=m+1;k<=limit;k++)if(pressure[k]<0){first_negative=2*k;break;}
 std::ofstream out(argv[3]);double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();out<<"{\n\"m\":"<<m<<",\n\"checked_through_degree\":"<<top<<",\n\"exact_fourier_residuals\":"<<top<<",\n\"first_post_cancellation_negative_degree\":"<<first_negative<<",\n\"maximum_vector_denominator_digits\":"<<maxdigits<<",\n\"runtime_seconds\":"<<sec<<",\n\"normalized_eigenvalue_even_coefficients\":[";for(int j=0;j<=limit;j++){if(j)out<<",";Q q=(j%2?-lam[2*j]:lam[2*j]);out<<"\""<<q<<"\"";}out<<"],\n\"pressure_even_coefficients\":[";for(int j=0;j<=limit;j++){if(j)out<<",";out<<"\""<<pressure[j]<<"\"";}out<<"]\n}\n";
 std::cout<<"m "<<m<<" first negative degree "<<first_negative<<"; "<<sec<<" seconds; maximum denominator digits "<<maxdigits<<"\n";
}
