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
 int E=A|B,identity=0;for(int u=0;u<n;++u)identity|=1<<(u*n+u);
 vector<int> seen(M,-1),powers;int power=identity;
 while(seen[power]<0){seen[power]=powers.size();powers.push_back(power);int next=0;for(int u=0;u<n;++u)next|=im[E][(power>>(n*u))&(Q-1)]<<(n*u);power=next;}
 int t=seen[power],p=powers.size()-t;
 auto at=[&](int x){return powers[x<(int)powers.size()?x:t+(x-t)%p];};
 auto st=[&](int x){int y=(x-t)%p;if(y<0)y+=p;return powers[t+y];};
 auto step=[&](const vector<int>&d,int S,int T){vector<int> nd(Q,-1);for(int C:{A,B}){int reset=im[C][S]&T;if(!reset)continue;for(int z=1;z<Q;++z)if(d[z]>=0){int zz=im[C][z]&T;int v=d[z]+(!zz);if(!zz)zz=reset;nd[zz]=max(nd[zz],v);}}return nd;};
 int best=bool(I&F);
 for(int N=1;N<2*t;++N){int S=I&im[rev[at(N)]][F];if(!S)continue;vector<int> dp(Q,-1);dp[S]=1;for(int x=0;x<N;++x){int T=im[at(x+1)][I]&im[rev[at(N-x-1)]][F];dp=step(dp,S,T);S=T;}best=max(best,*max_element(dp.begin(),dp.end()));}
 for(int r=0;r<p;++r){if(!(im[st(r)][I]&F))continue;
  int S=I&im[rev[st(r)]][F];vector<int> left(Q,-1);left[S]=1;
  for(int x=0;x<t;++x){int T=im[at(x+1)][I]&im[rev[st(r-x-1)]][F];left=step(left,S,T);S=T;}
  vector<int> stable(p);for(int a=0;a<p;++a)stable[a]=im[st(a)][I]&im[rev[st(r-a)]][F];
  vector<array<int,3>> edges;
  for(int a=0;a<p;++a){int aa=(a+1)%p;for(int z=stable[a];z;z=(z-1)&stable[a])for(int C:{A,B}){int reset=im[C][stable[a]]&stable[aa];if(!reset)continue;int zz=im[C][z]&stable[aa];int w=!zz;if(!zz)zz=reset;edges.push_back({a*Q+z,aa*Q+zz,w});}}
  vector<int> dist(p*Q,-1);for(int z=1;z<Q;++z)dist[(t%p)*Q+z]=left[z];
  int V=p*(Q-1);bool changed=false;
  for(int iteration=0;iteration<V;++iteration){changed=false;for(auto edge:edges){auto [u,v,w]=edge;if(dist[u]>=0&&dist[u]+w>dist[v]){dist[v]=dist[u]+w;changed=true;}}if(!changed)break;if(iteration==V-1)return {-1,t,p,0,0};}
  int end=(r-t)%p;if(end<0)end+=p;vector<int> dp(Q,-1);for(int z=1;z<Q;++z)dp[z]=dist[end*Q+z];
  S=im[st(r-t)][I]&im[rev[at(t)]][F];
  for(int x=0;x<t;++x){int T=im[st(r-t+x+1)][I]&im[rev[at(t-x-1)]][F];dp=step(dp,S,T);S=T;}
  best=max(best,*max_element(dp.begin(),dp.end()));
 }
 return {best,t,p,max(1,2*t+p*(Q-1)-1),0};
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
