// Owned finite-patch exact one-step expansion search.
#include <iostream>
#include <vector>
#include <array>
#include <set>
#include <tuple>
using namespace std;
#ifndef RAD
#define RAD 4
#endif
struct Act{int w,d,q;};Act T[600][2],U[600][2];
vector<int> qs,ctx[600];struct Case{int x,q,h,y;};
bool verify(int keep,const Case &c){int q=keep,h=0,x=c.x;set<tuple<int,int,int>> seen;for(int k=0;k<128;k++){if(k&&q==c.q&&h==c.h&&x==c.y)return true;if(h< -RAD||h>RAD||q==254)return false;if(!seen.insert({q,h,x}).second)return false;int bit=(x>>(h+RAD))&1;Act a=U[q][bit];x=(x&~(1<<(h+RAD)))|(a.w<<(h+RAD));h+=a.d;q=a.q;}return false;}
int main(){int n,p,start;cin>>n>>p>>start;for(int i=0;i<n;i++){int q,k;cin>>q;qs.push_back(q);for(int b=0;b<2;b++)cin>>T[q][b].w>>T[q][b].d>>T[q][b].q;cin>>k;while(k--){int x;cin>>x;ctx[q].push_back(x);}}
long tested=0,hits=0;
for(int i=0;i<p;i++){int drop,keep,same;cin>>drop>>keep>>same;auto phi=[&](int q){return q==drop?keep:q;};for(int q:qs)for(int b=0;b<2;b++){U[q][b]=T[q][b];U[q][b].q=phi(U[q][b].q);}
vector<Case> cases;for(int bit:{1-same,same})for(int origin:{drop,keep})for(int x:ctx[origin])if(((x>>RAD)&1)==bit){auto a=T[origin][bit];cases.push_back({x,phi(a.q),a.d,(x&~(1<<RAD))|(a.w<<RAD)});}
for(int w=0;w<2;w++)for(int d:{-1,1})for(int q:qs){if(q==drop)continue;U[keep][1-same]={w,d,q};tested++;bool ok=true;for(auto &c:cases)if(!verify(keep,c)){ok=false;break;}if(ok){hits++;cout<<"HIT "<<drop<<" "<<keep<<" "<<1-same<<" "<<w<<" "<<d<<" "<<q<<" cases "<<cases.size()<<endl;}}
if(i%50==0)cerr<<"PROGRESS "<<i<<" "<<tested<<" "<<hits<<endl;
}cout<<"DONE "<<tested<<" "<<hits<<endl;}
