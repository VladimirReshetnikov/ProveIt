#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <set>
#include <tuple>
#include <vector>
using namespace std;
struct Act {int w,d,n;bool operator==(const Act&o)const{return w==o.w&&d==o.d&&n==o.n;}};
Act rows[3000][2];
vector<int> states, eligible, ctx[3000][2];
int R,center,fullmask;
struct Conf {int q,h,t;};
vector<Conf> trajectories[3000][512];
bool usefuture=false;
int norm(int q,int a,int b){return q==a?b:q;}
bool simulate(int a,int b,int bit,Act ac,int source,int tape){
 Act target=rows[source][bit];
 int finalhead=center+(target.d?1:-1),finalstate=norm(target.n,a,b);
 int finaltape=(tape&~(1<<center))|(target.w<<center);
 int now=norm(ac.n,a,b),head=center+(ac.d?1:-1);
 tape=(tape&~(1<<center))|(ac.w<<center);
 for(int k=0;k<32;k++){
  if(now==finalstate && head==finalhead && tape==finaltape)return true;
  if(usefuture){for(auto target:trajectories[source][((finaltape&~(1<<center))|(bit<<center))])
    if(now==norm(target.q,a,b)&&head==target.h&&tape==target.t)return true;}
  if(head<0||head>2*R||now==254)return false;
  int rd=(tape>>head)&1; Act tr=rows[now][rd];
  if(now==b){if(rd!=bit)return false;tr=ac;}
  tape=(tape&~(1<<head))|(tr.w<<head);
  head+=tr.d?1:-1;now=norm(tr.n,a,b);
 }
 return false;
}
vector<Act> options(int a,int b,int bit){
 if(rows[a][bit]==rows[b][bit])return {rows[a][bit]};
 vector<Act> out;
 for(int n:states)if(n!=a)for(int d=0;d<2;d++)for(int w=0;w<2;w++){
  Act ac{w,d,n};bool ok=true;
  for(int q:{a,b}){
   for(int tape:ctx[q][bit])if(!simulate(a,b,bit,ac,q,tape)){ok=false;break;}
   if(!ok)break;
  }
  if(ok)out.push_back(ac);
 }
 return out;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);int nr,nq;usefuture=argc>2;
 f>>R>>nr;center=R;fullmask=(1<<(2*R+1))-1;
 for(int i=0;i<nr;i++){int q,b;Act ac;f>>q>>b>>ac.w>>ac.d>>ac.n;rows[q][b]=ac;if(!b)states.push_back(q);}
 states.push_back(254);f>>nq;
 for(int i=0;i<nq;i++){int q,n;f>>q>>n;eligible.push_back(q);for(int j=0;j<n;j++){int t;f>>t;ctx[q][(t>>center)&1].push_back(t);}}
 if(usefuture)for(int source:eligible)for(int bit=0;bit<2;bit++)for(int input:ctx[source][bit]){
  int q=source,h=center,t=input;
  for(int k=0;k<32;k++){
   if(h<0||h>2*R||q==254)break;
   auto ac=rows[q][(t>>h)&1];t=(t&~(1<<h))|(ac.w<<h);h+=ac.d?1:-1;q=ac.n;
   trajectories[source][input].push_back({q,h,t});
  }
 }
 int count=0,pairs=0;
 for(int i=0;i<nq;i++)for(int j=i+1;j<nq;j++){
  int a=eligible[i],b=eligible[j];pairs++;
  auto o0=options(a,b,0);if(o0.empty())continue;
  auto o1=options(a,b,1);if(o1.empty())continue;
  cout<<a<<' '<<b<<' '<<o0.size()<<' '<<o1.size();
  for(auto x:o0)cout<<' '<<x.w<<' '<<x.d<<' '<<x.n;
  for(auto x:o1)cout<<' '<<x.w<<' '<<x.d<<' '<<x.n;
  cout<<'\n';count++;
 }
 cerr<<"pairs "<<pairs<<" candidates "<<count<<'\n';
}
