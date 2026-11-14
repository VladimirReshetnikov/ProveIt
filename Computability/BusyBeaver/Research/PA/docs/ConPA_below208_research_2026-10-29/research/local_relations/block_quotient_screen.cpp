#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <set>
#include <random>
#include <cstdint>
using namespace std;
struct Tr{int w,d,z;};
constexpr int W=257,O=128;array<array<Tr,2>,1000> tm;
uint64_t zobrist[W];
struct Old{int q,h;uint64_t hash;};
struct Case{int q,b;array<unsigned char,W>t;vector<Old>old;};vector<Case> cases[1000];
int dropq,keepq,limitn=45;
bool simulate(const Case&c,int bit,Tr act){
 auto tape=c.t;int q=keepq,h=O;uint64_t hash=0;
 for(int i=0;i<limitn;i++){
  if(q==254||h<0||h>=W)return false;Tr a=q==keepq&&tape[h]==bit?act:tm[q][tape[h]];
  if(tape[h]!=a.w)hash^=zobrist[h];tape[h]=a.w;q=(a.z==dropq?keepq:a.z);h+=a.d;
  for(const auto &old:c.old)if(q==(old.q==dropq?keepq:old.q)&&h==old.h&&hash==old.hash)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc>3)limitn=stoi(argv[3]);ifstream f(argv[1]);string l;set<int>states;while(getline(f,l)){if(l.empty()||l[0]=='#')continue;int q,b,w,z;char d;istringstream s(l);s>>q>>b>>w>>d>>z;tm[q][b]={w,d=='R'?1:-1,z};states.insert(q);}
 mt19937_64 rng(76782371);for(auto&v:zobrist)v=rng();
 ifstream cf(argv[2]);while(getline(cf,l)){istringstream s(l);int q,b;s>>q>>b;Case c;c.q=q;c.b=b;string bits;s>>bits;if(bits.size()!=W)return 2;for(int i=0;i<W;i++)c.t[i]=bits[i]-'0';
  int h=O,p=q;uint64_t hash=0;auto tape=c.t;
  for(int i=0;i<limitn;i++){if(p==254||h<0||h>=W)break;auto a=tm[p][tape[h]];if(tape[h]!=a.w)hash^=zobrist[h];tape[h]=a.w;p=a.z;h+=a.d;c.old.push_back({p,h,hash});}
  cases[q].push_back(move(c));
 }
 long long pairs=0,actions=0,hits=0;
 if(argc>4&&string(argv[4])!="range"){ifstream hf(argv[4]);while(getline(hf,l)){istringstream s(l);string tag;s>>tag;if(tag!="HIT")continue;int bit,w,d,z;s>>dropq>>keepq>>bit>>w>>d>>z;Tr a{w,d,z};bool ok=true;actions++;
   for(int q:{dropq,keepq}){if(!ok)break;for(auto&c:cases[q])if(!simulate(c,bit,a)){ok=false;break;}}
   if(ok){hits++;cout<<"HIT "<<dropq<<" "<<keepq<<" "<<bit<<" "<<w<<" "<<d<<" "<<z<<endl;}
  }cout<<"DONE refinement actions "<<actions<<" hits "<<hits<<endl;return 0;}
 int lower=(argc>6&&string(argv[4])=="range")?stoi(argv[5]):1,upper=(argc>6&&string(argv[4])=="range")?stoi(argv[6]):1000;
 for(int drop:states){if(drop==0||drop<lower||drop>=upper)continue;dropq=drop;
  for(int keep:states){if(keep==drop)continue;keepq=keep;pairs++;
   for(int bit=0;bit<2;bit++)for(int z:states){if(z==drop)continue;for(int d:{-1,1})for(int w:{0,1}){actions++;Tr a{w,d,z};bool ok=true;
    for(int q:{drop,keep}){if(!ok)break;for(auto&c:cases[q])if(!simulate(c,bit,a)){ok=false;break;}}
    if(ok){hits++;cout<<"HIT "<<drop<<" "<<keep<<" "<<bit<<" "<<w<<" "<<d<<" "<<z<<endl;}
   }}
  }
  if(drop%10==0)cerr<<"PROGRESS "<<drop<<" pairs "<<pairs<<" actions "<<actions<<" hits "<<hits<<endl;
 }
 cout<<"DONE pairs "<<pairs<<" actions "<<actions<<" hits "<<hits<<endl;
}
