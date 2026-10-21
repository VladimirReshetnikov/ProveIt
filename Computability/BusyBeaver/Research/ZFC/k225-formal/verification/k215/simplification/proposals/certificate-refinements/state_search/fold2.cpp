// Context-sensitive two-row fold screen. This is synthesis, not a proof assistant.
// Each changed row's proof may not inspect the other changed row. Thus local
// proofs compose without presuming an unverified candidate row.
#include <array>
#include <vector>
#include <iostream>
#include <cstdint>
#include <algorithm>
using U=__uint128_t;
struct Act {int w,d,q; bool operator==(Act a)const{return w==a.w&&d==a.d&&q==a.q;}};
struct Ctx {U known=0, val=0;};
struct Node {int h,q,n; U known,val,diff;};
std::array<std::array<Act,2>,1000> T;
std::vector<int> Q;
std::array<std::vector<Ctx>,1000> C;
int maxstep=45, maxnodes=200;
U bit(int h){return U(1)<<(h+60);}
bool block(int old,int keep,int drop,int b,Act act,Ctx ctx,bool forbidOther){
 U z=bit(0); if((ctx.known&z)&&bool(ctx.val&z)!=b)return true;
 ctx.known|=z; if(b)ctx.val|=z;else ctx.val&=~z;
 Act a0=T[old][b];int goal=a0.q==drop?keep:a0.q;
 U goalDiff=a0.w==b?0:z;
 std::vector<Node> todo{{0,keep,0,ctx.known,ctx.val,0}};
 int count=0;
 while(!todo.empty()){
  Node a=todo.back();todo.pop_back();if(++count>maxnodes)return false;
  if(a.n&&a.h==a0.d&&a.q==goal&&a.diff==goalDiff)continue;
  if(a.n>=maxstep||a.q<0||a.q>=1000||T[a.q][0].q==-2)return false;
  if(a.h < -59||a.h>59)return false;
  U hbit=bit(a.h);bool known=a.known&hbit;
  for(int rb=0;rb<2;++rb){
   if(known&&rb!=bool((a.val^a.diff)&hbit))continue;
   Node n=a;n.n++;n.known|=hbit;
   if(!known){if(rb)n.val|=hbit;else n.val&=~hbit;}
   if(forbidOther&&a.q==keep&&rb!=b)return false;
   Act x=a.q==keep&&rb==b?act:T[a.q][rb];
   n.q=x.q==drop?keep:x.q;n.h+=x.d;
   if(x.w==bool(n.val&hbit))n.diff&=~hbit;else n.diff|=hbit;
   todo.push_back(n);
  }
 }
 return true;
}
bool all(int q,int r,int b,Act act,bool forbidOther){
 for(int old:{q,r})for(Ctx c:C[old])
  if(!block(old,q,r,b,act,c,forbidOther))return false;
 return true;
}
int main(){
 for(auto &r:T)for(auto &a:r)a={0,0,-2};
 int nq;std::cin>>nq>>maxstep>>maxnodes;
 for(int i=0;i<nq;++i){int q;std::cin>>q;Q.push_back(q);for(int b=0;b<2;++b)std::cin>>T[q][b].w>>T[q][b].d>>T[q][b].q;}
 int nc;std::cin>>nc;for(int i=0;i<nc;++i){int q,n;std::cin>>q>>n;for(int j=0;j<n;++j){int k;std::cin>>k;Ctx c;for(int t=0;t<k;++t){int h,v;std::cin>>h>>v;c.known|=bit(h);if(v)c.val|=bit(h);}C[q].push_back(c);}}
 int np;std::cin>>np;long long tried=0;int partial=0,survivors=0;
 for(int i=0;i<np;++i){
  int q,r;std::cin>>q>>r;std::array<std::vector<Act>,2> choices;
  for(int b=0;b<2;++b){
   Act x=T[q][b],y=T[r][b];if(x.q==r)x.q=q;if(y.q==r)y.q=q;
   if(x==y){choices[b].push_back(x);continue;}
   bool otherDiff=!(T[q][1-b]==T[r][1-b]);
   for(int w=0;w<2;++w)for(int d:{-1,1})for(int t:Q){
    if(t==r)continue;
    ++tried;Act a={w,d,t};if(all(q,r,b,a,otherDiff))choices[b].push_back(a);
   }
   if(choices[b].empty())break;
  }
  if(!choices[0].empty())++partial;
  if(!choices[0].empty()&&!choices[1].empty()){
   ++survivors;for(Act x:choices[0])for(Act y:choices[1])
   std::cout<<"SURVIVOR "<<q<<' '<<r<<' '<<x.w<<' '<<x.d<<' '<<x.q<<' '<<y.w<<' '<<y.d<<' '<<y.q<<std::endl;
  }
 }
 std::cout<<"RESULT pairs "<<np<<" actions "<<tried<<" partial "<<partial<<" surviving_pairs "<<survivors<<std::endl;
}
