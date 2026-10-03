#include <algorithm>
#include <array>
#include <iostream>
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
int main(int argc,char**argv){n=argc>1?atoi(argv[1]):3;Q=1<<n;M=1<<(n*n);
 im.assign(M,vector<int>(Q));rev.resize(M);
 for(int A=0;A<M;++A){for(int z=1;z<Q;++z){int bit=z&-z;int u=__builtin_ctz((unsigned)bit);im[A][z]=im[A][z^bit]|((A>>(n*u))&(Q-1));}
  for(int u=0;u<n;++u)for(int v=0;v<n;++v)if(A>>(u*n+v)&1)rev[A]|=1<<(v*n+u);
 }
 vector<vector<int>> perms;vector<int> p;for(int u=0;u<n;++u)p.push_back(u);do{perms.push_back(p);}while(next_permutation(p.begin(),p.end()));
 vector<vector<int>> pm(perms.size(),vector<int>(M));for(int i=0;i<(int)perms.size();++i)for(int A=0;A<M;++A)pm[i][A]=permute_matrix(A,perms[i]);
 map<int,long long> counts;long long networks=0,total=0;int global=-1;map<int,array<int,8>> examples;int maxh=0;
 for(int A=0;A<M;++A)for(int B=A;B<M;++B){int id=A*M+B;set<int> orbit;
  bool canonical=true;for(int i=0;i<(int)perms.size();++i){int a=pm[i][A],b=pm[i][B];orbit.insert(a*M+b);orbit.insert(b*M+a);if(min(a*M+b,b*M+a)<id){canonical=false;break;}}
  if(!canonical)continue;++networks;
  for(int I=1;I<Q;++I)for(int F=1;F<Q;++F){auto z=solve(A,B,I,F);counts[z.rank]+=orbit.size();total+=orbit.size();maxh=max(maxh,z.H);
   if(!examples.count(z.rank))examples[z.rank]={A,B,I,F,z.length,z.t,z.p,z.H};
   if(z.rank>global){global=z.rank;cerr<<"NEW MAX "<<global<<" A "<<A<<" B "<<B<<" I "<<I<<" F "<<F<<" length "<<z.length<<" networks "<<networks<<"\n";}
  }
 }
 cout<<"{\n  \"n\": "<<n<<",\n  \"canonical_transition_pairs\": "<<networks<<",\n  \"total_labeled_nfas\": "<<total<<",\n  \"maximum_finite_rank\": "<<global<<",\n  \"maximum_finite_horizon\": "<<maxh<<",\n  \"counts\": {";
 bool first=true;for(auto [r,c]:counts){if(!first)cout<<",";first=false;cout<<"\n    \""<<(r<0?string("infinite"):to_string(r))<<"\": "<<c;}cout<<"\n  },\n  \"examples\": {";first=true;
 for(auto [r,a]:examples){if(!first)cout<<",";first=false;cout<<"\n    \""<<(r<0?string("infinite"):to_string(r))<<"\": [";for(int i=0;i<8;++i){if(i)cout<<",";cout<<a[i];}cout<<"]";}cout<<"\n  }\n}\n";
}
