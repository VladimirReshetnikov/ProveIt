// Exact residue certificate using the centered three-term recurrence.
#include <array>
#include <cstdint>
#include <iostream>
using I=std::int64_t;
using Jet=std::array<I,7>;
I mod(I x,I p){x%=p;return x<0?x+p:x;}
int main(){
 const int D=6,R=1571,Q=3048; const I P[2]={1000003,1000033};
 std::uint64_t cells=0,holes=0,extra=0; I digest[2]={0,0};
 for(int q=0;q<Q;++q){
  Jet a[2]{},b[2]{};a[0][0]=a[1][0]=1;
  for(int j=0;j<13+q;++j)for(int h=0;h<2;++h){Jet c{};for(int i=0;i<=D;++i)c[i]=mod((12-j)*a[h][i]+(i?a[h][i-1]:0),P[h]);a[h]=c;}
  for(int k=0;k<R-1;++k){
   bool hole=q==12 && k%2==0;bool zero=true;
   for(int h=0;h<2;++h){I v=k==0?a[h][D]:b[h][D];zero&=v==0;digest[h]=mod(1009*digest[h]+v,P[h]);if(hole&&v!=0){std::cerr<<"hole failed";return 2;}}
   ++cells;if(hole)++holes;else if(zero){++extra;std::cerr<<"unresolved "<<k<<' '<<q<<'\n';}
   if(k==0){for(int h=0;h<2;++h)for(int i=0;i<=D;++i)b[h][i]=mod((12-q)*a[h][i]+(i?2*a[h][i-1]:0),P[h]);}
   else for(int h=0;h<2;++h){Jet c{};for(int i=0;i<=D;++i)c[i]=mod((12-q)*b[h][i]+(i?2*b[h][i-1]:0)+I(k)*(k+13+q)*a[h][i],P[h]);a[h]=b[h];b[h]=c;}
  }
 }
 if(extra||cells!=4785360||holes!=785)return 1;
 std::cout<<"{\"depth\":6,\"k_max\":1569,\"q_max\":3047,\"cells\":"<<cells<<",\"holes\":"<<holes<<",\"unresolved_nonholes\":"<<extra<<",\"moduli\":[1000003,1000033],\"rolling_checksums\":["<<digest[0]<<','<<digest[1]<<"],\"max_derivative_order\":6198,\"status\":\"PASS\"}\n";
}
