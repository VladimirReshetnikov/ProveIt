#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <set>
#include <random>
using namespace std;
struct Tr{int w,d,z;bool operator==(const Tr&x)const{return w==x.w&&d==x.d&&z==x.z;}};
constexpr int W=257,O=128;array<array<Tr,2>,1000> tm;
struct Case{int q,b;array<unsigned char,W>t;};vector<Case> cases[1000][2];
int dropq,keepq,limitn=31;
int rho(int q){return q==dropq?keepq:q;}
bool simulate(const Case&c,Tr a0,Tr a1){
 auto tape=c.t;Tr old=tm[c.q][c.b];auto expected=c.t;expected[O]=old.w;int mismatches=(tape[O]!=expected[O]);int q=keepq,h=O;
 for(int i=0;i<limitn;i++){
  if(q==254||h<0||h>=W)return false;Tr a=q==keepq?(tape[h]?a1:a0):tm[q][tape[h]];
  mismatches-=tape[h]!=expected[h];tape[h]=a.w;mismatches+=tape[h]!=expected[h];q=rho(a.z);h+=a.d;
  if(q==rho(old.z)&&h==O+old.d&&!mismatches)return true;
 }
 return false;
}
bool branch(int b,Tr action){
 Tr a0=b?tm[keepq][0]:action,a1=b?action:tm[keepq][1];
 for(int q:{dropq,keepq})for(auto&c:cases[q][b])if(!simulate(c,a0,a1))return false;
 return true;
}
bool partial_case(const Case&c,int bit,Tr action){
 auto tape=c.t;Tr old=tm[c.q][c.b];auto expected=c.t;expected[O]=old.w;int mismatches=tape[O]!=expected[O],q=keepq,h=O;
 for(int i=0;i<limitn;i++){
  if(q==254||h<0||h>=W)return false;
  if(q==keepq&&tape[h]!=bit)return true;
  Tr a=q==keepq?action:tm[q][tape[h]];
  mismatches-=tape[h]!=expected[h];tape[h]=a.w;mismatches+=tape[h]!=expected[h];q=rho(a.z);h+=a.d;
  if(q==rho(old.z)&&h==O+old.d&&!mismatches)return true;
 }return false;
}
bool partial_branch(int b,Tr a){for(int q:{dropq,keepq})for(auto&c:cases[q][b])if(!partial_case(c,b,a))return false;return true;}
int main(int argc,char**argv){
 if(argc<3){cerr<<"Usage: search TABLE CONTEXTS [BOUND] [PAIR_FILE]\n";return 2;} if(argc>3)limitn=stoi(argv[3]);if(limitn<1||limitn>120){cerr<<"BOUND must be1..120\n";return 2;} ifstream f(argv[1]);if(!f){cerr<<"Cannot open table\n";return 2;}string l;set<int>states;while(getline(f,l)){if(l.empty()||l[0]=='#')continue;int q,b,w,z;char d;istringstream s(l);s>>q>>b>>w>>d>>z;tm[q][b]={w,d=='R'?1:-1,z};states.insert(q);}
 mt19937 rng(20261030);ifstream cf(argv[2]);if(!cf){cerr<<"Cannot open contexts\n";return 2;}while(getline(cf,l)){istringstream s(l);int q,n;s>>q>>n;vector<pair<int,int>>ctx;int at,bit;while(s>>at>>bit)ctx.push_back({at,bit});
  for(int b=0;b<2;b++){bool bad=false;for(auto [p,v]:ctx)if(p==0&&v!=b)bad=true;if(bad)continue;
   for(int rep=0;rep<3;rep++){Case c;c.q=q;c.b=b;for(auto&v:c.t)v=rng()%2;for(auto [p,v]:ctx)c.t[O+p]=v;c.t[O]=b;cases[q][b].push_back(c);}}
 }
 long long pairs=0,actions=0,firsts=0,seconds=0,hits=0;
 set<pair<int,int>>only;if(argc>4){ifstream pf(argv[4]);int a,b;while(pf>>a>>b)only.insert({a,b});}
 for(int drop:states){if(drop==0)continue;dropq=drop;
  for(int keep:states){if(keep>=drop)continue;keepq=keep;
   if(!only.empty()&&!only.count({drop,keep}))continue;
   pairs++;
   array<vector<Tr>,2> good;for(int b=0;b<2;b++){
    for(int z:states){if(z==drop)continue;for(int d:{-1,1})for(int w:{0,1}){actions++;Tr a{w,d,z};if(partial_branch(b,a))good[b].push_back(a);}}
    if(good[b].empty())break;
   }
   if(good[0].empty())continue;firsts++;
   if(good[1].empty())continue;seconds++;
   if(!only.empty())cerr<<"PAIR "<<drop<<" "<<keep<<" domains "<<good[0].size()<<" "<<good[1].size()<<endl;
   for(auto a0:good[0])for(auto a1:good[1]){bool ok=true;for(int q:{drop,keep}){if(!ok)break;for(int b=0;b<2;b++){if(!ok)break;for(auto&c:cases[q][b])if(!simulate(c,a0,a1)){ok=false;break;}}}
    if(ok){hits++;cout<<"HIT "<<drop<<" "<<keep<<" "<<a0.w<<" "<<a0.d<<" "<<a0.z<<" "<<a1.w<<" "<<a1.d<<" "<<a1.z<<endl;}}
  }
  if(drop%10==0)cerr<<"PROGRESS "<<drop<<" pairs "<<pairs<<" first "<<firsts<<" second "<<seconds<<endl;
 }
 cout<<"DONE pairs "<<pairs<<" actions "<<actions<<" first "<<firsts<<" second "<<seconds<<" hits "<<hits<<endl;
}
