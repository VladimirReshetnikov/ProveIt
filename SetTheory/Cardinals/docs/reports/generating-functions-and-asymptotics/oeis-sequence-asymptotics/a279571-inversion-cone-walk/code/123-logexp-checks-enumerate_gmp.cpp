// Exact prefix/suffix recurrence for the published two-color generating tree.
#include <gmpxx.h>
#include <vector>
#include <iostream>
#include <fstream>
#include <cstdlib>
using I=mpz_class;
using V=std::vector<std::vector<I>>;
V matrix(int n){V x(n+2);for(int a=0;a<=n+1;++a)x[a].resize(n+2-a);return x;}
I get(const V& x,int a,int b){if(a<0||b<0||a>=int(x.size())||b>=int(x[a].size()))return 0;return x[a][b];}
int main(int argc,char**argv){int N=argc>1?std::atoi(argv[1]):1000;V P=matrix(0),Q=matrix(0);P[0][0]=1;std::cout<<"0 1\n";
for(int n=0;n<N;++n){V U=matrix(n+1),W=matrix(n+1);I total=0;
 for(int t=1;t<=n+1;++t){I sp=0,sq=0;for(int b=0;b<t;++b){sp+=get(P,t-1-b,b);sq+=get(Q,t-b,b);U[t-b][b]=sp+sq;total+=U[t-b][b];}}
 for(int A=1;A<=n+1;++A){I tail=0;for(int b=n+1-A;b>=0;--b){W[A][b]=tail;total+=tail;tail+=get(P,A-1,b)+get(Q,A-1,b);}}
 P.swap(U);Q.swap(W);std::cout<<n+1<<' '<<total<<'\n';if((n+1)%100==0){std::cout.flush();std::cerr<<"completed "<<n+1<<'\n';}}
}
