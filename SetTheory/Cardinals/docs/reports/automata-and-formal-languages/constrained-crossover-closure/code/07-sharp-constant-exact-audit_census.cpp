// Independent audit: direct labeled enumeration, pair-orbit periods,
// explicit prefix/core/suffix graph, Tarjan SCCs and condensed-DAG optimization.
// Does not import producer code; no state/letter symmetry quotient is used.
#include <algorithm>
#include <array>
#include <cassert>
#include <functional>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <queue>
#include <vector>
using namespace std;
struct Arc{int to,w;};
struct Graph{
 vector<vector<Arc>> out; vector<vector<int>> in;
 int node(){out.emplace_back();in.emplace_back();return out.size()-1;}
 void edge(int a,int b,int w){assert(a>=0&&b>=0);out[a].push_back({b,w});in[b].push_back(a);}
 int maximum(int src,int sink){
  int n=out.size();vector<char> reach(n),finish(n);
  vector<int> todo={src};reach[src]=true;
  for(size_t k=0;k<todo.size();++k)for(auto e:out[todo[k]])if(!reach[e.to]){reach[e.to]=true;todo.push_back(e.to);}
  todo={sink};finish[sink]=true;
  for(size_t k=0;k<todo.size();++k)for(int u:in[todo[k]])if(!finish[u]){finish[u]=true;todo.push_back(u);}
  if(!reach[sink])return 0;
  vector<int> dfs(n,-1),low(n),component(n,-1),stack;vector<char> on(n);int tick=0,nc=0;
  function<void(int)> visit=[&](int u){dfs[u]=low[u]=tick++;stack.push_back(u);on[u]=true;
   for(auto e:out[u])if(reach[e.to]&&finish[e.to]){int v=e.to;if(dfs[v]<0){visit(v);low[u]=min(low[u],low[v]);}else if(on[v])low[u]=min(low[u],dfs[v]);}
   if(low[u]==dfs[u]){while(true){int v=stack.back();stack.pop_back();on[v]=false;component[v]=nc;if(v==u)break;}++nc;}
  };
  visit(src);vector<vector<Arc>> dag(nc);vector<int> degree(nc);
  for(int u=0;u<n;++u)if(component[u]>=0)for(auto e:out[u])if(component[e.to]>=0){int a=component[u],b=component[e.to];if(a==b){if(e.w)return -1;}else{dag[a].push_back({b,e.w});++degree[b];}}
  queue<int> ready;for(int k=0;k<nc;++k)if(!degree[k])ready.push(k);
  vector<int> value(nc,-1000000);value[component[src]]=1;
  while(!ready.empty()){int u=ready.front();ready.pop();for(auto e:dag[u]){value[e.to]=max(value[e.to],value[u]+e.w);if(!--degree[e.to])ready.push(e.to);}}
  return value[component[sink]];
 }
};
struct Orbit{int t,p;vector<int> P,R;int idx(int k)const{if(k>=0&&k<(int)P.size())return k;int rem=(k-t)%p;if(rem<0)rem+=p;return t+rem;}int pf(int k)const{return P[idx(k)];}int rb(int k)const{return R[idx(k)];}int ps(int k)const{int rem=(k-t)%p;if(rem<0)rem+=p;return P[t+rem];}int rs(int k)const{int rem=(k-t)%p;if(rem<0)rem+=p;return R[t+rem];}};
int n,q,m;vector<vector<int>> fw,backward;
Orbit make_orbit(int E,int I,int F){
 Orbit o;vector<int> seen(q*q,-1);int x=I,y=F;
 while(seen[x*q+y]<0){seen[x*q+y]=o.P.size();o.P.push_back(x);o.R.push_back(y);x=fw[E][x];y=backward[E][y];}
 o.t=seen[x*q+y];o.p=o.P.size()-o.t;return o;
}
vector<int> step(const vector<int>&v,int S,int T,int A,int B){
 vector<int> ans(q,-1);
 for(int z=1;z<q;++z)if(v[z]>=0)for(int C:{A,B}){int start=fw[C][S]&T;if(!start)continue;int next=fw[C][z]&T;bool cut=!next;if(cut)next=start;ans[next]=max(ans[next],v[z]+cut);}
 return ans;
}
int evaluate(int A,int B,int I,int F,const Orbit&o){
 int best=(I&F)?1:0;
 for(int len=1;len<2*o.t;++len){int S=I&o.rb(len);if(!S)continue;vector<int> dp(q,-1);dp[S]=1;for(int i=0;i<len;++i){int T=o.pf(i+1)&o.rb(len-i-1);dp=step(dp,S,T,A,B);S=T;}best=max(best,*max_element(dp.begin(),dp.end()));}
 for(int r=0;r<o.p;++r){if(!(o.ps(r)&F))continue;
  vector<int> ls(o.t+1),rs(o.t+1),ms(o.p);
  for(int i=0;i<=o.t;++i){ls[i]=o.pf(i)&o.rs(r-i);rs[i]=o.ps(r-o.t+i)&o.rb(o.t-i);}
  for(int a=0;a<o.p;++a)ms[a]=o.ps(a)&o.rs(r-a);
  Graph g;vector<vector<int>> L(o.t+1,vector<int>(q,-1)),M(o.p,vector<int>(q,-1)),R(o.t+1,vector<int>(q,-1));
  auto alloc=[&](vector<int>&ids,int S){for(int z=1;z<q;++z)if((z&S)==z)ids[z]=g.node();};
  for(int a=0;a<o.p;++a)alloc(M[a],ms[a]);
  for(int i=0;i<o.t;++i){alloc(L[i],ls[i]);}
  L[o.t]=M[o.t%o.p];
  for(int i=0;i<=o.t;++i){alloc(R[i],rs[i]);}
  int sink=g.node();
  auto transitions=[&](const vector<int>&from,const vector<int>&to,int S,int T){for(int z=1;z<q;++z)if(from[z]>=0)for(int C:{A,B}){int a=fw[C][S]&T;if(!a)continue;int b=fw[C][z]&T;int w=b?0:1;if(!b)b=a;g.edge(from[z],to[b],w);}};
  for(int i=0;i<o.t;++i)transitions(L[i],L[i+1],ls[i],ls[i+1]);
  for(int a=0;a<o.p;++a)transitions(M[a],M[(a+1)%o.p],ms[a],ms[(a+1)%o.p]);
  int end=((r-o.t)%o.p+o.p)%o.p;
  assert(ms[end]==rs[0]);for(int z=1;z<q;++z)if(M[end][z]>=0)g.edge(M[end][z],R[0][z],0);
  for(int i=0;i<o.t;++i)transitions(R[i],R[i+1],rs[i],rs[i+1]);
  for(int z=1;z<q;++z)if(R[o.t][z]>=0)g.edge(R[o.t][z],sink,0);
  int value=g.maximum(L[0][ls[0]],sink);if(value<0)return -1;best=max(best,value);
 }
 return best;
}
int main(int argc,char**argv){
 n=argc>1?atoi(argv[1]):3;assert(n>=1&&n<=3);q=1<<n;m=1<<(n*n);
 fw.assign(m,vector<int>(q));backward=fw;
 for(int C=0;C<m;++C)for(int z=0;z<q;++z)for(int u=0;u<n;++u)for(int v=0;v<n;++v)if(C&(1<<(n*u+v))){if(z&(1<<u))fw[C][z]|=1<<v;if(z&(1<<v))backward[C][z]|=1<<u;}
 vector<Orbit> orbits(m*q*q);for(int E=0;E<m;++E)for(int I=1;I<q;++I)for(int F=1;F<q;++F)orbits[(E*q+I)*q+F]=make_orbit(E,I,F);
 map<int,long long> counts;long long total=0;int maxh=0;vector<array<int,4>> maxcases;int maxrank=0;
 for(int A=0;A<m;++A)for(int B=0;B<m;++B)for(int I=1;I<q;++I)for(int F=1;F<q;++F){const auto&o=orbits[((A|B)*q+I)*q+F];int value=evaluate(A,B,I,F,o);++counts[value];++total;if(value>=0)maxh=max(maxh,max(1,2*o.t+o.p*(q-1)-1));if(value>maxrank){maxrank=value;maxcases.clear();}if(value==maxrank)maxcases.push_back({A,B,I,F});}
 cout<<"{\n\"states\":"<<n<<",\n\"total_directly_enumerated\":"<<total<<",\n\"maximum_finite_horizon\":"<<maxh<<",\n\"counts\":{";bool comma=false;for(auto[r,c]:counts){if(comma)cout<<",";comma=true;cout<<"\""<<(r==-1?string("infinite"):to_string(r))<<"\":"<<c;}cout<<"},\n\"maximum_finite_rank\":"<<maxrank<<",\n\"maximizers\":[";comma=false;for(auto a:maxcases){if(comma)cout<<",";comma=true;cout<<"["<<a[0]<<","<<a[1]<<","<<a[2]<<","<<a[3]<<"]";}cout<<"]\n}\n";
 return 0;
}
