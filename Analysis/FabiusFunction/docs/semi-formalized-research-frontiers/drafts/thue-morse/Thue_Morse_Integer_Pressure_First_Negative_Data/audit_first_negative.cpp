// Independent a posteriori certificate replay. No producer rounding solve is used.
#include <gmpxx.h>
#include <zlib.h>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using Z=mpz_class; using V=std::vector<Z>; using M=std::vector<V>;
void need(bool b,const char*s){if(!b)throw std::runtime_error(s);}
Z ab(const Z&z){return z<0?-z:z;}
Z gcd(const Z&a,const Z&b){Z r;mpz_gcd(r.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return r;}
Z lcm(const Z&a,const Z&b){Z r;mpz_lcm(r.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return r;}
Z floorq(const Z&a,const Z&b){Z r;mpz_fdiv_q(r.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return r;}
Z ceilq(const Z&a,const Z&b){return -floorq(-a,b);}
V mv(const M&a,const V&x){V y(a.size());for(size_t i=0;i<a.size();++i)for(size_t j=0;j<x.size();++j)y[i]+=a[i][j]*x[j];return y;}
V polymul(const V&a,const V&b){V z(a.size()+b.size()-1);for(size_t i=0;i<a.size();++i)for(size_t j=0;j<b.size();++j)z[i+j]+=a[i]*b[j];return z;}
Z ws(const V&x){Z z=x[0];for(size_t i=1;i<x.size();++i)z+=2*x[i];return z;}
Z wn(const V&x){Z z=ab(x[0]);for(size_t i=1;i<x.size();++i)z+=2*ab(x[i]);return z;}
std::string line(gzFile f){std::string s;char b[65536];while(gzgets(f,b,sizeof b)){s+=b;if(!s.empty()&&s.back()=='\n')return s;}return s;}
struct State{V u,y;Z e,lam,le,norm;};
int main(int argc,char**argv){try{
 need(argc==3,"usage source.trace.gz output.json");auto start=std::chrono::steady_clock::now();
 gzFile in=gzopen(argv[1],"rb");need(in!=nullptr,"open trace");std::string magic;int m,d,prec;{std::istringstream s(line(in));s>>magic>>m>>d>>prec;}
 need(m>=2&&d==2*m&&magic=="TMPFIRST1"&&prec>=0,"scope/header");int N=d-1,c=m-1,top=4*d-2,limit=4*m-1;
 Z scale(line(in));V given(4);{std::istringstream s(line(in));for(auto&v:given)s>>v;need(bool(s),"norm metadata");}
 Z fact;mpz_fac_ui(fact.get_mpz_t(),N);Z expected=Z(1)<<prec;for(int i=0;i<5;i++)expected*=fact;need(scale==expected,"grid scale");
 Z D=Z(1)<<(d-1);
 M choose(top+1);for(int n=0;n<=top;n++){choose[n]=V(n+1);choose[n][0]=choose[n][n]=1;for(int j=1;j<n;j++)choose[n][j]=choose[n-1][j-1]+choose[n-1][j];}
 auto bi=[&](int n,int k)->Z{return k<0||k>n?Z(0):choose[n][k];};
 M B(N,V(N));for(int i=0;i<N;i++)for(int j=0;j<N;j++)B[i][j]=bi(d,m+2*(i-c)-(j-c));
 for(int j=0;j<N;j++){Z total=0;for(int i=0;i<N;i++)total+=B[i][j];need(total==D,"full column stochasticity");}
 M ep(N+1);ep[1]=V{1};for(int p=2;p<=N;p++){ep[p]=V(p);for(int k=0;k<p;k++){if(k<p-1)ep[p][k]+=(k+1)*ep[p-1][k];if(k)ep[p][k]+=(p-k)*ep[p-1][k-1];}}
 M E(N,V(N)),S(N,V(N));for(int r=0;r<N;r++){V q(r+1);for(int k=0;k<=r;k++)q[k]=(k%2?-1:1)*choose[r][k];auto col=polymul(q,ep[N-r]);for(int i=0;i<N;i++)E[i][r]=col[i];}
 for(int i=0;i<N;i++){V poly{1};for(int h=-i;h<N-i;h++)poly=polymul(poly,V{h,1});for(int r=0;r<N;r++)S[r][i]=poly[N-r];}
 for(int r=0;r<N;r++){V x(N);for(int i=0;i<N;i++)x[i]=E[i][r];auto a=mv(S,x),b=mv(B,x);for(int i=0;i<N;i++){need(a[i]==(i==r?fact:Z(0)),"full integer inverse");need(b[i]==(D>>r)*x[i],"full eigensystem");}}
 Z L=1;for(int r=1;r<N;r++)L=lcm(L,(Z(1)<<r)-1);V weight(N);for(int r=1;r<N;r++)weight[r]=(Z(1)<<r)*(L/((Z(1)<<r)-1));Z td=fact*L;
 Z ae=0,ao=0;for(int j=0;j<m;j++){Z norm=0;for(int k=0;k<m;k++){Z z=0;for(int r=2;r<N;r+=2){Z sr=S[r][c+j];if(j)sr+=S[r][c-j];z+=(E[c+k][r]*sr)*weight[r];}norm+=(k?2:1)*ab(z);}if(j==0)norm*=2;if(norm>ae)ae=norm;}
 for(int j=1;j<m;j++){Z norm=0;for(int k=1;k<m;k++){Z z=0;for(int r=1;r<N;r+=2)z+=(E[c+k][r]*(S[r][c+j]-S[r][c-j]))*weight[r];norm+=ab(z);}if(norm>ao)ao=norm;}
 Z aed=2*td,aod=td;need(ae*given[1]==given[0]*aed&&ao*given[3]==given[2]*aod,"independent full-matrix norms");
 std::cerr<<"m "<<m<<" norms checked\n";
 M Be(m,V(m)),Bo(m,V(m));for(int k=0;k<m;k++)for(int j=0;j<m;j++){Be[k][j]=B[c+k][c+j]+(j?B[c+k][c-j]:Z(0));Bo[k][j]=j?Z(B[c+k][c+j]-B[c+k][c-j]):Z(0);}
 V initial(m);for(int i=0;i<m;i++)initial[i]=ep[N][c+i];
 M K(d+1,V(m));for(int j=0;j<=d;j++)for(int k=0;k<m;k++)for(int u=0;u<=j;u++)K[j][k]+=(u%2?-1:1)*bi(m+k,u)*bi(m-k,j-u);
 std::vector<State> states;std::string radfile=std::string(argv[2])+".radii.gz";gzFile radout=gzopen(radfile.c_str(),"wb1");need(radout!=nullptr,"radii output");
 gzprintf(radout,"TMPFIRST_RESIDUAL1 %d %d\n",m,prec);
 auto writez=[&](const Z&z){auto s=z.get_str();need(gzwrite(radout,s.data(),s.size())==(int)s.size(),"radii write");gzwrite(radout," ",1);};
 for(int order=0;order<=top;order++){
  std::istringstream src(line(in));int idx;Z olde,oldle;State st;st.u=V(m);src>>idx>>olde>>st.lam>>oldle;for(auto&x:st.u)src>>x;need(bool(src)&&idx==order&&olde>=0&&oldle>=0,"trace state");
  st.y=mv(order%2?Bo:Be,st.u);st.norm=wn(st.u);
  if(order==0){need(olde==0&&oldle==0&&st.lam==scale,"initial scalar");for(int i=0;i<m;i++)need(st.u[i]==initial[i]*(scale/fact),"initial vector");need(ws(st.u)==scale,"initial norm");st.e=st.le=0;}
  else{
   need(order%2?st.u[0]==0:ws(st.u)==0,"exact vector normalization");
   V rn(m);Z eb=0;for(int j=1;j<=std::min(order,d);j++){const auto&old=states[order-j];for(int k=0;k<m;k++)rn[k]+=K[j][k]*old.y[k];eb+=choose[d][j]*old.e;}
   if(order%2||order<d){need(st.lam==0,"structural scalar zero");st.le=0;}else{need(st.lam==floorq(ws(rn),D),"scalar center");st.le=eb+1;}
   V rhs(m);for(int i=0;i<m;i++)rhs[i]=scale*rn[i];Z pe=0;
   for(int j=d;j<order;j+=2){const auto&a=states[j];const auto&b=states[order-j];for(int i=0;i<m;i++)rhs[i]-=D*a.lam*b.u[i];pe+=ab(a.lam)*b.e+a.le*b.norm+a.le*b.e;}
   Z erhs=eb+ceilq(pe,scale),psum=order%2?Z(0):ws(rhs);V defect(m);
   for(int i=0;i<m;i++)defect[i]=fact*(scale*(D*st.u[i]-st.y[i])-rhs[i])+psum*initial[i];
   need(order%2?defect[0]==0:ws(defect)==0,"projected residual normalization");
   Z dn=wn(defect),dd=fact*D*scale,an=order%2?ao:ae,ad=order%2?aod:aed;
   st.e=ceilq(an*(erhs*dd+dn),ad*dd);
  }
  gzprintf(radout,"%d ",order);writez(st.e);writez(st.le);gzwrite(radout,"\n",1);states.push_back(std::move(st));
 }
 need(line(in).empty(),"no extra trace state");need(gzclose(in)==Z_OK,"trace close");need(gzclose(radout)==Z_OK,"radii close");
 std::cerr<<"m "<<m<<" residuals propagated\n";
 V tj(top+2);tj[1]=1;for(int n=2;n<=top;n+=2)for(int j=1;j<n;j+=2)tj[n+1]+=choose[n][j]*tj[j]*tj[n-j];
 M powers(limit+1,V(limit+1));powers[0][0]=1;for(int j=1;j<=limit;j++)for(int k=j;k<=limit;k++)for(int s=1;s<=k-j+1;s++)powers[j][k]+=choose[2*k][2*s]*tj[2*s+1]*powers[j-1][k-s];
 V low(limit+1),high(limit+1);for(int j=m;j<=limit;j++){Z center=(j%2?-1:1)*states[2*j].lam;low[j]=center-states[2*j].le;high[j]=center+states[2*j].le;}
 V sqlo(limit+1),sqhi(limit+1),cubelo(limit+1),cubehi(limit+1);
 auto product=[](const Z&a,const Z&b,const Z&c,const Z&d){V v{Z(a*c),Z(a*d),Z(b*c),Z(b*d)};return std::pair<Z,Z>{*std::min_element(v.begin(),v.end()),*std::max_element(v.begin(),v.end())};};
 for(int j=2*m;j<=limit;j++)for(int k=m;k<=j-m;k++){auto p=product(low[k],high[k],low[j-k],high[j-k]);sqlo[j]+=p.first;sqhi[j]+=p.second;}
 for(int j=3*m;j<=limit;j++)for(int k=2*m;k<=j-m;k++){auto p=product(sqlo[k],sqhi[k],low[j-k],high[j-k]);cubelo[j]+=p.first;cubehi[j]+=p.second;}
 V loglo(limit+1),loghi(limit+1);for(int j=m;j<=limit;j++){
 loglo[j]=6*scale*scale*low[j]-3*scale*sqhi[j]+2*cubelo[j];
 loghi[j]=6*scale*scale*high[j]-3*scale*sqlo[j]+2*cubehi[j];}
 std::ofstream out(argv[2]);need(bool(out),"output open");out<<"{\"m\":"<<m<<",\"method\":\"independent projected residual enclosures\",\"trace_orders\":"<<top+1<<",\"strict_pressure_degrees\":"<<3*m-1<<",\"full_spectral_norms_verified\":true,\"pressure_conversion\":\"independent tangent ODE derivative jets\",\"pressure_bounds\":[\n";
 bool positive=true;int first_negative=0,first_inconclusive=0;for(int k=m;k<=limit;k++){Z lo=-12*m*scale*scale*scale*tj[2*k-1],hi=lo;for(int j=m;j<=k;j++){lo+=loglo[j]*powers[j][k];hi+=loghi[j]*powers[j][k];}need(lo<=hi,"pressure interval order");if(k==m)need(lo<=0&&hi>=0,"missing coefficient");else{if(lo<=0&&hi>=0){positive=false;if(!first_inconclusive)first_inconclusive=2*k;}if(hi<0&&!first_negative)first_negative=2*k;}Z factorial;mpz_fac_ui(factorial.get_mpz_t(),2*k);Z den=6*scale*scale*scale*factorial,g=gcd(gcd(lo,hi),den);lo/=g;hi/=g;den/=g;if(k>m)out<<",\n";out<<"{\"degree\":"<<2*k<<",\"lower_numerator\":\""<<lo<<"\",\"upper_numerator\":\""<<hi<<"\",\"denominator\":\""<<den<<"\"}";}
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 out<<"\n],\"all_nonzero_signs_certified\":"<<(positive?"true":"false")<<",\"first_negative_degree\":"<<first_negative<<",\"first_inconclusive_degree\":"<<first_inconclusive<<",\"first_negative_certified\":"<<((first_negative>0&&(!first_inconclusive||first_inconclusive>first_negative))?"true":"false")<<",\"seconds\":"<<seconds<<"}\n";out.close();need(bool(out),"output close");
 std::cout<<"m "<<m<<" residual "<<(positive?"all signs":"inconclusive")<<" first negative "<<first_negative<<" "<<seconds<<" seconds\n";return (first_negative>0&&(!first_inconclusive||first_inconclusive>first_negative))?0:2;
 }catch(const std::exception&e){std::cerr<<"FAIL "<<e.what()<<"\n";return 1;}}

