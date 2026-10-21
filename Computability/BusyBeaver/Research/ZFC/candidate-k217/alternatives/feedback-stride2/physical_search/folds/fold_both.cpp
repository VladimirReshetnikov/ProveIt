// Owned two-branch alias synthesis: exact patches, no interior merged state.
#include <iostream>
#include <vector>
#include <array>
#include <tuple>
using namespace std;
#ifndef RAD
#define RAD 4
#endif
struct Act{int w,d,q;};Act T[600][2];vector<int> qs,ctx[600];struct Case{int x,q,h,y;};
bool verify(int drop,int keep,Act first,const Case &c){int q=keep,h=0,x=c.x;array<tuple<int,int,int>,64> seen;for(int k=0;k<64;k++){if(k&&q==c.q&&h==c.h&&x==c.y)return true;if(h< -RAD||h>RAD||q==254||(k&&q==keep))return false;for(int j=0;j<k;j++)if(seen[j]==make_tuple(q,h,x))return false;seen[k]={q,h,x};int bit=(x>>(h+RAD))&1;Act a=k?T[q][bit]:first;x=(x&~(1<<(h+RAD)))|(a.w<<(h+RAD));h+=a.d;q=a.q==drop?keep:a.q;}return false;}
int main(){int n,p,start;cin>>n>>p>>start;for(int i=0;i<n;i++){int q,k;cin>>q;qs.push_back(q);for(int b=0;b<2;b++)cin>>T[q][b].w>>T[q][b].d>>T[q][b].q;cin>>k;while(k--){int x;cin>>x;ctx[q].push_back(x);}}
long tested=0,pairs=0,hits=0;for(int drop:qs)if(drop!=start)for(int keep:qs)if(keep!=drop){pairs++;auto phi=[&](int q){return q==drop?keep:q;};vector<Act> answers[2];for(int bit=0;bit<2;bit++){vector<Case> cases;for(int origin:{drop,keep})for(int x:ctx[origin])if(((x>>RAD)&1)==bit){auto a=T[origin][bit];cases.push_back({x,phi(a.q),a.d,(x&~(1<<RAD))|(a.w<<RAD)});}
for(int w=0;w<2;w++)for(int d:{-1,1})for(int q:qs){if(q==drop)continue;Act act{w,d,q};tested++;bool ok=true;for(auto &c:cases)if(!verify(drop,keep,act,c)){ok=false;break;}if(ok)answers[bit].push_back(act);}if(answers[bit].empty())break;}
if(!answers[0].empty()&&!answers[1].empty()){hits++;cout<<"HIT "<<drop<<" "<<keep;for(int bit=0;bit<2;bit++){auto a=answers[bit][0];cout<<" ["<<a.w<<" "<<a.d<<" "<<a.q<<"]";}cout<<endl;}
if(pairs%1000==0)cerr<<"PROGRESS "<<pairs<<" "<<tested<<" "<<hits<<endl;
}cout<<"DONE "<<pairs<<" "<<tested<<" "<<hits<<endl;}
