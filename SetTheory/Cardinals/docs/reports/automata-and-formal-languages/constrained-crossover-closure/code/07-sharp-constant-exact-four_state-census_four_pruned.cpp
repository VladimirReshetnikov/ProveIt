#include <algorithm>
#include <array>
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <vector>
using namespace std;
struct Result { int rank,t,p,H,length; };
int n,Q,M;
vector<vector<int>> im;
vector<int> rev;
Result solve(int A,int B,int I,int F){
 int E=A|B; int er=rev[E]; int seen[256]; fill(seen,seen+256,-1);
 int ps[256],rs[256],len=0,P=I,R=F;
 while(seen[P*Q+R]<0){seen[P*Q+R]=len; ps[len]=P;rs[len]=R;++len;P=im[E][P];R=im[er][R];}
 int t=seen[P*Q+R],p=len-t;
 auto st=[&](int a){int b=(a-t)%p;if(b<0)b+=p;return t+b;};
 for(int residue=0;residue<p;++residue){
  if(!(ps[st(residue)]&F))continue;
  int S[256];for(int a=0;a<p;++a)S[a]=ps[st(a)]&rs[st(residue-a)];
  bool visited[2048]={};int que[2048],tail=0;int a0=t%p;
  que[tail++]=a0*Q+S[a0];visited[que[0]]=true;
  for(int head=0;head<tail;++head){int z=que[head]%Q,a=que[head]/Q,aa=(a+1)%p;
   for(int C:{A,B}){if(!(im[C][S[a]]&S[aa]))continue;int zz=im[C][z]&S[aa];
    if(!zz)return {-1,t,p,0,0};int state=aa*Q+zz;if(!visited[state]){visited[state]=true;que[tail++]=state;}
   }
  }
 }
 int H=max(1,2*t+p*(Q-1)-1);int pp[2048],rr[2048];
 for(int x=0;x<=H;++x){int k=x<len?x:t+(x-t)%p;pp[x]=ps[k];rr[x]=rs[k];}
 int best=bool(I&F),blen=0;
 for(int N=1;N<=H;++N){int S[2048];for(int x=0;x<=N;++x)S[x]=pp[x]&rr[N-x];if(!S[0])continue;
  int dp[16],nd[16];fill(dp,dp+Q,-1);dp[S[0]]=1;
  for(int x=0;x<N;++x){fill(nd,nd+Q,-1);
   for(int C:{A,B}){int restart=im[C][S[x]]&S[x+1];if(!restart)continue;
    for(int z=1;z<Q;++z)if(dp[z]>=0){int zz=im[C][z]&S[x+1];int v=dp[z]+(!zz);if(!zz)zz=restart;nd[zz]=max(nd[zz],v);}
   }copy(nd,nd+Q,dp);
  }
  int val=*max_element(dp,dp+Q);if(val>best){best=val;blen=N;}
 }
 return {best,t,p,H,blen};
}
int permute_matrix(int A,const vector<int>&p){int B=0;for(int u=0;u<n;++u)for(int v=0;v<n;++v)if(A>>(u*n+v)&1)B|=1<<(p[u]*n+p[v]);return B;}
int main(){n=4;Q=16;M=65536;im.assign(M,vector<int>(Q));rev.resize(M);for(int A=0;A<M;++A){for(int z=1;z<Q;++z){int bit=z&-z,u=__builtin_ctz((unsigned)bit);im[A][z]=im[A][z^bit]|((A>>(n*u))&(Q-1));}for(int u=0;u<n;++u)for(int v=0;v<n;++v)if(A>>(u*n+v)&1)rev[A]|=1<<(v*n+u);}
map<int,vector<array<int,2>>> work;ifstream in("four-state-high-transient-pairs.txt");if(!in){cerr<<"Missing four-state-high-transient-pairs.txt; run candidate generation first\n";return 1;}int E,I,F,t;while(in>>E>>I>>F>>t)work[E].push_back({I,F});long long tested=0;int best=0,done=0;map<int,long long> counts;
for(auto [E,pairs]:work){vector<int> bits;for(int v=0;v<16;++v)if(E>>v&1)bits.push_back(1<<v);long long labels=1;for(auto b:bits)labels*=3;
for(int code=0;code<labels;++code){int z=code,A=0,B=0;for(int bit:bits){int x=z%3;z/=3;if(x!=1)A|=bit;if(x!=0)B|=bit;}if(A>B)continue;
for(auto pair:pairs){I=pair[0];F=pair[1];auto r=solve(A,B,I,F);++tested;++counts[r.rank];if(r.rank>best){best=r.rank;cout<<"BEST "<<best<<" E "<<E<<" A "<<A<<" B "<<B<<" I "<<I<<" F "<<F<<" length "<<r.length<<" t "<<r.t<<" p "<<r.p<<" tested "<<tested<<endl;}}
}
if(++done%25==0)cout<<"PROGRESS graphs "<<done<<" tested "<<tested<<" best "<<best<<endl;
}
cout<<"DONE graphs "<<done<<" tested "<<tested<<" best "<<best<<endl;for(auto [r,c]:counts)cout<<"RANK "<<r<<" COUNT "<<c<<endl;
}