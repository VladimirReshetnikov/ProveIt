// Independent direct Fourier-product quadrature in IEEE binary128 (113 bits).
// Uses libquadmath, not the Taylor/cumulant acceleration in diagnostics.py.
#include <quadmath.h>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <cmath>
#include <string>
using Q=__float128;
void out(const char*name,Q x){char b[256];quadmath_snprintf(b,sizeof(b),"%.34Qg",x);printf("%s %s\n",name,b);}
int main(int argc,char**argv){
 if(argc<3){fprintf(stderr,"usage: quad113 input_case.txt nodes.txt\n");return 2;}
 FILE *in=fopen(argv[1],"r");int a,J,count;char buf[256],nb[256];long long n;fscanf(in,"%d %255s %255s %d %d",&a,buf,nb,&J,&count);Q K=strtoflt128(buf,0);n=atoll(nb);
 std::vector<long long> ks(count);for(auto &k:ks)fscanf(in,"%lld",&k);fclose(in);
 std::vector<Q> q(count),h(count),v(count);Q p1,t,W,C,V,U,T1,T2,Qcond,cR,cS,res;long long m,baseR,baseS;
 for(int it=0;it<5;it++){
   t=a*logq(K)/K;W=K/(a*(logq(K)-1));m=(long long)floorq(K);baseR=m-1;baseS=m*(m+1)/2-1;
   p1=1/(1+expq(t));cR=0;cS=p1;U=0;T1=0;T2=0;
   for(int i=0;i<count;i++){Q k=ks[i];Q f=a*logq(k)-t*k;q[i]=1/(1+expq(fabsq(f)));h[i]=ks[i]<=m?-1:1;v[i]=q[i]*(1-q[i]);Q d=k-K;cR+=h[i]*q[i];cS+=h[i]*k*q[i];U+=v[i];T1+=d*v[i];T2+=d*d*v[i];}
   C=K*U+T1;V=K*K*U+2*K*T1+T2+p1*(1-p1);res=(Q)(baseS-n)+cS;
   if(it<4)K-=res*K*W/V;
 }
 Qcond=(U*T2-T1*T1+U*p1*(1-p1))/V;
 const Q pi=acosq(-1),rootV=sqrtq(V),mu=cR-floorq(cR);out("K",K);out("mean_residual",res);out("mu_mod1",mu);out("Q",Qcond);
 FILE *nd=fopen(argv[2],"r");int N;fscanf(nd,"%d",&N);std::vector<Q> ys(N),ws(N);for(int i=0;i<N;i++){char s1[256],s2[256];fscanf(nd,"%255s %255s",s1,s2);ys[i]=strtoflt128(s1,0);ws[i]=strtoflt128(s2,0);}fclose(nd);
 Q total=0;
 for(int j=0;j<=J;j++){
   Q integ=0;
   for(int l=0;l<N;l++){
      Q theta=2*pi*j*C/V+ys[l]/rootV,lr=0,li=-2*pi*j*mu+theta*res;
      for(int i=0;i<count;i++){
         Q beta=h[i]*(theta*ks[i]-2*pi*j);Q sh=sinq(beta/2),cbm=-2*sh*sh,sb=sinq(beta);
         lr+=log1pq(2*v[i]*cbm)/2;
         li+=atan2q(q[i]*sb,1+q[i]*cbm)-q[i]*beta;
      }
      Q sh=sinq(theta/2),cbm=-2*sh*sh,sb=sinq(theta);
      lr+=log1pq(2*p1*(1-p1)*cbm)/2;
      li+=atan2q(p1*sb,1+p1*cbm)-p1*theta;
      integ+=ws[l]*expq(lr)*cosq(li)/sqrtq(2*pi);
   }
   out((std::string("satellite_")+std::to_string(j)).c_str(),integ);
   total+=(j==0?1:2)*integ;fflush(stdout);
 }
 out("multiplier",total);
}
