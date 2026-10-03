// Exact normalized eigenvalue and pressure recursion using a row-polynomial gauge.
// The gauge is similar to V_a, but each Taylor matrix is diag(K_j(k))*A.
#include <gmpxx.h>
#include <zlib.h>
#include <climits>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using Z=mpz_class;using Q=mpq_class;using Vec=std::vector<Z>;using Mat=std::vector<Vec>;
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
int main(int argc,char**argv){req(argc==4,"usage m precision_bits output.json");int m=std::stoi(argv[1]),d=2*m,n=d-1,top=3*d-2;req(m>=2,"m must be at least2");auto start=std::chrono::steady_clock::now();Z D=Z(1)<<(d-1);Vec bin(d+1);for(int j=0;j<=d;j++)mpz_bin_uiui(bin[j].get_mpz_t(),d,j);
 n=m;std::vector<int>ix(n);for(int i=0;i<n;i++)ix[i]=i;
 Mat Be(n,Vec(n)),Bo(n,Vec(n));auto entry=[&](int k,int r)->Z{int p=m+2*k-r;return 0<=p&&p<=d?bin[p]:Z(0);};
 for(int k=0;k<n;k++)for(int r=0;r<n;r++){Be[k][r]=entry(k,r)+(r?entry(k,-r):Z(0));if(r)Bo[k][r]=entry(k,r)-entry(k,-r);}
 int N=d-1;Mat Ef(N,Vec(N)),Sf(N,Vec(N));std::vector<Vec> ep(N+1);ep[1]=Vec{Z(1)};
 for(int p=2;p<=N;p++){ep[p]=Vec(p);for(int k=0;k<p;k++){if(k<p-1)ep[p][k]+=(k+1)*ep[p-1][k];if(k)ep[p][k]+=(p-k)*ep[p-1][k-1];}}
 for(int r=0;r<N;r++){Vec coeff(r+1);for(int k=0;k<=r;k++){mpz_bin_uiui(coeff[k].get_mpz_t(),r,k);if(k%2)coeff[k]=-coeff[k];}for(int k=0;k<=r;k++)for(int j=0;j<N-r;j++)Ef[k+j][r]+=coeff[k]*ep[N-r][j];}
 for(int i=0;i<N;i++){Vec poly{Z(1)};for(int h=-i;h<=N-1-i;h++){Vec next(poly.size()+1);for(size_t j=0;j<poly.size();j++){next[j]+=h*poly[j];next[j+1]+=poly[j];}poly=std::move(next);}for(int r=0;r<N;r++)Sf[r][i]=poly[N-r];}
 Mat Ee(n,Vec(n)),Se(n,Vec(n)),Eo(n-1,Vec(n-1)),So(n-1,Vec(n-1));Z specfac;mpz_fac_ui(specfac.get_mpz_t(),N);
 for(int k=0;k<n;k++)for(int j=0;j<n;j++){Ee[k][j]=Ef[m-1+k][2*j];Se[j][k]=Sf[2*j][m-1+k]*(k?2:1);}
 for(int k=1;k<n;k++)for(int j=0;j<n-1;j++){Eo[k-1][j]=Ef[m-1+k][2*j+1];So[j][k-1]=2*Sf[2*j+1][m-1+k];}
 auto check_inverse=[&](const Mat&S,const Mat&E){for(size_t j=0;j<E.size();j++){Vec col(E.size());for(size_t i=0;i<E.size();i++)col[i]=E[i][j];auto v=mv(S,col);for(size_t i=0;i<E.size();i++)req(v[i]==(i==j?specfac:Z(0)),"explicit Eulerian inverse");}};check_inverse(Se,Ee);check_inverse(So,Eo);
 for(int j=0;j<n;j++){Vec col(n);for(int k=0;k<n;k++)col[k]=Ee[k][j];auto v=mv(Be,col);for(int k=0;k<n;k++)req(v[k]==(D>>(2*j))*col[k],"even spectral eigenvector");}
 for(int j=0;j<n-1;j++){Vec col(n);for(int k=1;k<n;k++)col[k]=Eo[k-1][j];auto v=mv(Bo,col);for(int k=0;k<n;k++)req(v[k]==(D>>(2*j+1))*col[k],"odd spectral eigenvector");}
 Z Le=1,Lo=1;for(int r=1;r<N;r++){Z b=(Z(1)<<r)-1;if(r%2)Lo=lz(Lo,b);else Le=lz(Le,b);}Vec we(n),wo(n-1);for(int j=1;j<n;j++)we[j]=(Z(1)<<(2*j))*(Le/((Z(1)<<(2*j))-1));for(int j=0;j<n-1;j++)wo[j]=(Z(1)<<(2*j+1))*(Lo/((Z(1)<<(2*j+1))-1));
 Vec full(1,Z(1));for(int r=2;r<=d-1;r++){Vec v(r);for(int k=0;k<r;k++){if(k<(int)full.size())v[k]+=(k+1)*full[k];if(k)v[k]+=(r-k)*full[k-1];}full=std::move(v);}Vec eul(n);for(int k=0;k<n;k++)eul[k]=full[m-1+k];Z fact;mpz_fac_ui(fact.get_mpz_t(),d-1);norm(eul,fact);req(weighted_sum(eul)==fact,"h0 sum");Vec y0=mv(Be,eul);for(int i=0;i<n;i++)req(y0[i]==D*eul[i],"h0 residual");Z yd=fact;norm(y0,yd);
 Mat K(d+1,Vec(n));for(int i=0;i<n;i++){K[0][i]=1;K[1][i]=-2*ix[i];for(int j=1;j<d;j++){Z z=(-2*ix[i])*K[j][i]-(d-j+1)*K[j-1][i];req(mpz_divisible_ui_p(z.get_mpz_t(),j+1),"Krawtchouk exact");mpz_divexact_ui(K[j+1][i].get_mpz_t(),z.get_mpz_t(),j+1);}}

 int precision=std::stoi(argv[2]);req(precision>=0,"nonnegative precision");Z scale=(Z(1)<<precision);for(int j=0;j<5;j++)scale*=specfac;
 auto alpha_norm=[&](const Mat&E,const Mat&S,const Vec&w,bool odd)->std::pair<Z,Z>{Z numerator=0;int n=E.size();for(int j=0;j<n;j++){Vec v(n);for(int i=0;i<n;i++)v[i]=S[i][j]*w[i];v=mv(E,v);Z z=0;for(int i=0;i<n;i++)z+=(odd?1:(i?2:1))*abs(v[i]);if(!odd&&j==0)z*=2;if(z>numerator)numerator=z;}Z denominator=odd?Z(specfac*Lo):Z(2*specfac*Le);return {numerator,denominator};};
 auto ae=alpha_norm(Ee,Se,we,false),ao=alpha_norm(Eo,So,wo,true);
 std::vector<Vec>hs(1,Vec(n)),ys;std::vector<Z>error(1,Z(0)),unorm;std::vector<Z>ell(top+1),le(top+1);ell[0]=scale;
 for(int i=0;i<n;i++)hs[0][i]=eul[i]*(scale/fact);ys.push_back(mv(Be,hs[0]));unorm.push_back(scale);
 auto ceildiv=[](const Z&a,const Z&b){Z z;mpz_cdiv_q(z.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return z;};
 auto floor=[](const Z&a,const Z&b){Z z;mpz_fdiv_q(z.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return z;};
 std::string output=argv[3],tracename=output+".trace.gz";gzFile trace=gzopen(tracename.c_str(),"wb1");req(trace!=nullptr,"trace open");
 auto writez=[&](const Z&z){auto v=z.get_str();req(gzwrite(trace,v.data(),v.size())==(int)v.size(),"trace write");gzwrite(trace," ",1);};
 gzprintf(trace,"TMPRES1 %d %d %d\n",m,d,precision);writez(scale);gzwrite(trace,"\n",1);writez(ae.first);writez(ae.second);writez(ao.first);writez(ao.second);gzwrite(trace,"\n",1);
 auto trace_order=[&](int order){gzprintf(trace,"%d ",order);writez(error[order]);writez(ell[order]);writez(le[order]);for(auto&v:hs[order])writez(v);gzwrite(trace,"\n",1);};trace_order(0);
 for(int order=1;order<=top;order++){
  Vec rn(n);Z eb=0;
  for(int j=1;j<=std::min(order,d);j++){for(int i=0;i<n;i++)rn[i]+=K[j][i]*ys[order-j][i];eb+=bin[j]*error[order-j];}
  if(order%2){req(rn[0]==0,"odd rhs coordinate");ell[order]=0;le[order]=0;}
  else if(order<d){ell[order]=0;le[order]=0;}
  else{ell[order]=floor(weighted_sum(rn),D);le[order]=eb+1;}
  Vec rhs(n);for(int i=0;i<n;i++)rhs[i]=scale*rn[i];Z product_error=0;
  for(int j=d;j<order;j+=2){int h=order-j;if(ell[j]!=0)for(int i=0;i<n;i++)rhs[i]-=D*ell[j]*hs[h][i];product_error+=abs(ell[j])*error[h]+le[j]*unorm[h]+le[j]*error[h];}
  Z erhs=eb+ceildiv(product_error,scale);Vec num;Z denom;
  if(order%2){Vec rr(rhs.begin()+1,rhs.end());auto v=mv(So,rr);for(int j=0;j<n-1;j++)v[j]*=wo[j];auto z=mv(Eo,v);num.push_back(0);num.insert(num.end(),z.begin(),z.end());denom=specfac*D*Lo*scale;}
  else{auto v=mv(Se,rhs);for(int j=0;j<n;j++)v[j]*=we[j];num=mv(Ee,v);denom=specfac*D*Le*scale;req(weighted_sum(num)==0,"projected solution normalization");}
  Vec hn(n);for(int i=1;i<n;i++){hn[i]=floor(num[i],denom);req(hn[i]*denom<=num[i]&&num[i]<(hn[i]+1)*denom,"outward grid floor");}
  if(!(order%2)){for(int i=1;i<n;i++)hn[0]-=2*hn[i];req(weighted_sum(hn)==0,"grid normalization");}
  auto alpha=order%2?ao:ae;Z rad=ceildiv(alpha.first*erhs,alpha.second)+(order%2?2:4)*(m-1);
  hs.push_back(std::move(hn));error.push_back(std::move(rad));ys.push_back(mv(order%2?Bo:Be,hs.back()));Z norm=abs(hs.back()[0]);for(int i=1;i<n;i++)norm+=2*abs(hs.back()[i]);unorm.push_back(norm);trace_order(order);
  if(order%40==0){double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cerr<<"m "<<m<<" interval order "<<order<<" / "<<top<<" secs "<<sec<<"\n";}
 }
 req(gzclose(trace)==Z_OK,"trace close");
 int limit=3*m-1;std::vector<Vec>tanpow(limit+1,Vec(limit+2));tanpow[0][0]=1;
 for(int k=0;k<limit;k++)for(int j=1;j<=k+1;j++){int p=2*j;tanpow[k+1][j]=p*(p-1)*tanpow[k][j-1]+2*p*p*tanpow[k][j]+p*(p+1)*tanpow[k][j+1];}
 Vec lv(limit+1),lr(limit+1),lc(limit+1),er(limit+1);
 for(int j=m;j<=limit;j++){lv[j]=(j%2?-ell[2*j]:ell[2*j]);lr[j]=le[2*j];}
 for(int j=m;j<=limit;j++){lc[j]=2*scale*lv[j];er[j]=2*scale*lr[j];for(int k=m;k<=j-m;k++){lc[j]-=lv[k]*lv[j-k];er[j]+=abs(lv[k])*lr[j-k]+abs(lv[j-k])*lr[k]+lr[k]*lr[j-k];}}
 std::ofstream out(output);out<<"{\n\"m\":"<<m<<",\n\"precision_bits\":"<<precision<<",\n\"scale\":\""<<scale<<"\",\n\"checked_response_orders\":"<<top<<",\n\"spectral_identities_checked\":true,\n\"directed_integer_enclosures\":true,\n\"pressure_bounds\":[\n";bool good=true;int minmargin=INT_MAX;
 for(int k=m;k<=limit;k++){
  Z center=-4*m*scale*scale*tanpow[k-1][1],radius=0;
  for(int j=m;j<=k;j++){center+=lc[j]*tanpow[k][j];radius+=er[j]*tanpow[k][j];}
  Z lower=center-radius,upper=center+radius,f;mpz_fac_ui(f.get_mpz_t(),2*k);Z denominator=2*scale*scale*f;
  if(k==m)req(lower<=0&&upper>=0,"missing coefficient enclosed");else{if(lower<=0)good=false;if(radius>0)minmargin=std::min(minmargin,(int)mpz_sizeinbase(center.get_mpz_t(),2)-(int)mpz_sizeinbase(radius.get_mpz_t(),2));}
  Z divisor=gz(gz(lower,upper),denominator);lower/=divisor;upper/=divisor;denominator/=divisor;
  if(k>m)out<<",\n";out<<"{\"degree\":"<<2*k<<",\"lower_numerator\":\""<<lower<<"\",\"upper_numerator\":\""<<upper<<"\",\"denominator\":\""<<denominator<<"\"}";
 }
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();out<<"\n],\n\"all_requested_lower_bounds_positive\":"<<(good?"true":"false")<<",\n\"minimum_margin_bits\":"<<minmargin<<",\n\"runtime_seconds\":"<<sec<<"\n}\n";
 std::cout<<"m "<<m<<" interval "<<(good?"positive":"inconclusive")<<"; "<<sec<<" seconds; margin bits "<<minmargin<<"\n";return good?0:2;
}
