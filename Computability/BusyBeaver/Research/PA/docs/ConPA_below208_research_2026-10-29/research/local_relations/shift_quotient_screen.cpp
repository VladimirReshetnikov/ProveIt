#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <set>
#include <random>
using namespace std;
struct Tr{int w,d,z;};
constexpr int W=257,O=128;array<array<Tr,2>,1000> tm;
struct Case{int q,b;array<unsigned char,W>t;};vector<Case> cases[1000][2];
int dropq,keepq,offset,limitn=71;
bool simulate(const Case&c,int bit,Tr act){
 auto tape=c.t;Tr old=tm[c.q][c.b];auto expected=c.t;expected[O]=old.w;int mismatches=tape[O]!=expected[O];int q=keepq,h=O+(c.q==dropq?offset:0);int es=old.z,eh=O+old.d;if(es==dropq){es=keepq;eh+=offset;}
 for(int i=0;i<limitn;i++){
  if(q==254||h<0||h>=W)return false;Tr a=q==keepq&&tape[h]==bit?act:tm[q][tape[h]];
  mismatches-=tape[h]!=expected[h];tape[h]=a.w;mismatches+=tape[h]!=expected[h];if(a.z==dropq){q=keepq;h-=a.d;}else{q=a.z;h+=a.d;}
  if(q==es&&h==eh&&!mismatches)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc>3)limitn=stoi(argv[3]);ifstream f(argv[1]);string l;set<int>states;while(getline(f,l)){if(l.empty()||l[0]=='#')continue;int q,b,w,z;char d;istringstream s(l);s>>q>>b>>w>>d>>z;tm[q][b]={w,d=='R'?1:-1,z};states.insert(q);}
 mt19937 rng(510292);ifstream cf(argv[2]);while(getline(cf,l)){istringstream s(l);int q,n;s>>q>>n;vector<pair<int,int>>ctx;int at,bit;while(s>>at>>bit)ctx.push_back({at,bit});
  for(int b=0;b<2;b++){bool bad=false;for(auto [p,v]:ctx)if(p==0&&v!=b)bad=true;if(bad)continue;
   for(int rep=0;rep<2;rep++){Case c;c.q=q;c.b=b;for(auto&v:c.t)v=rng()%2;for(auto [p,v]:ctx)c.t[O+p]=v;c.t[O]=b;cases[q][b].push_back(c);}}
 }
 long long pairs=0,actions=0,hits=0;
 for(int drop:states){if(drop==0)continue;set<int>dirs;for(int p:states)for(int b=0;b<2;b++)if(tm[p][b].z==drop)dirs.insert(tm[p][b].d);if(dirs.size()!=1)continue;dropq=drop;offset=-2**dirs.begin();
  for(int keep:states){if(keep==drop)continue;keepq=keep;pairs++;
   for(int bit=0;bit<2;bit++)for(int z:states){if(z==drop)continue;for(int d:{-1,1})for(int w:{0,1}){actions++;Tr a{w,d,z};bool ok=true;
    for(int q:{drop,keep}){if(!ok)break;for(int b=0;b<2;b++){if(!ok)break;for(auto&c:cases[q][b])if(!simulate(c,bit,a)){ok=false;break;}}}
    if(ok){hits++;cout<<"HIT "<<drop<<" "<<keep<<" "<<offset<<" "<<bit<<" "<<w<<" "<<d<<" "<<z<<endl;}
   }}
  }
  if(drop%10==0)cerr<<"PROGRESS "<<drop<<" pairs "<<pairs<<" actions "<<actions<<" hits "<<hits<<endl;
 }
 cout<<"DONE pairs "<<pairs<<" actions "<<actions<<" hits "<<hits<<endl;
}
