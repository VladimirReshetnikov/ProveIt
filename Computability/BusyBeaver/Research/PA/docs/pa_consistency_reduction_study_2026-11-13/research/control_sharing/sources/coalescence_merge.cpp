#include <iostream>
#include <fstream>
#include <sstream>
#include <array>
#include <map>
#include <vector>
#include <queue>
#include <algorithm>
#include <cstdlib>
#include <bitset>
#include <unordered_set>
#include <chrono>
using namespace std;
struct A{int w,d,n;};
struct Good{bitset<2500>v;int oldsteps,newsteps;};
struct Ctx{int p;unordered_set<uint64_t> targets; bool halt=false;};
uint64_t key(int q,int h,int t){return uint64_t(q)<<32|uint64_t(h+32)<<24|t;}
int main(int argc,char**argv){
 if(argc<6){cerr<<"usage: table radius oldbound newbound contexts\n";return 2;}
 ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,MASK=N-1,OLD=atoi(argv[3]),NEW=atoi(argv[4]);
 A rows[2500][2];bool exists[2500]={};int q,b,w,n;char d;vector<int>states;
 string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};if(!exists[q])states.push_back(q);exists[q]=true;}
 sort(states.begin(),states.end());
 map<int,array<vector<Ctx>,2>>patterns;
 ifstream pin(argv[5]);int rq,rp;long long oldconfigcount=0;
 while(pin>>rq>>rp){Ctx ct;ct.p=rp;int c=rq,h=0,t=rp;
  for(int step=1;step<=OLD;step++){
   if(h< -K||h>K||!exists[c])break;
   A op=rows[c][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
   if(c==254){ct.halt=true;break;}
   if(!ct.targets.insert(key(c,h,t)).second)break;
  }
  oldconfigcount+=ct.targets.size();patterns[rq][rp>>K&1].push_back(move(ct));
 }
 cerr<<"oldconfigs "<<oldconfigcount<<endl;
 map<int,array<map<int,Good>,2>>solutions;
 vector<A>actions;for(int n:states)for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,n});actions.push_back({0,1,254});
 for(int q:states){for(int b=0;b<2;b++){
  for(int ai=0;ai<(int)actions.size();ai++){A first=actions[ai];bool okay=true;bitset<2500>vis;int maxsteps=0;
   for(auto const&ct:patterns[q][b]){int p=ct.p;int c=first.n,h=first.d,t=(p&~(1<<K))|(first.w<<K);bool hit=false;
    for(int st=1;st<=NEW;st++){
     if((ct.halt&&c==254)||ct.targets.count(key(c,h,t))){hit=true;maxsteps=max(maxsteps,st);break;}
     if(c==q||h < -K||h>K||c<0||c>=2500||!exists[c])break;
     vis[c]=true;A op=rows[c][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
    }if(!hit){okay=false;break;}
   }if(okay)solutions[q][b][ai]={vis,OLD,maxsteps};
  }
 }cerr<<"Q "<<q<<" choices "<<solutions[q][0].size()<<' '<<solutions[q][1].size()<<endl;}
 for(int a:states){if(patterns[a][0].empty()&&patterns[a][1].empty())continue;for(int r:states){if(a>=r||patterns[r][0].empty()&&patterns[r][1].empty())continue;array<vector<int>,2>choices;
  for(int b=0;b<2;b++)for(auto const&[ai,g]:solutions[a][b]){auto it=solutions[r][b].find(ai);if(it!=solutions[r][b].end()&&!g.v[r]&&!it->second.v[a])choices[b].push_back(ai);}
  if(choices[0].empty()||choices[1].empty())continue;
  cout<<"{\"remove\":"<<a<<",\"keep\":"<<r<<",\"choices\":[";
  for(int b=0;b<2;b++){if(b)cout<<',';cout<<'[';bool sep=false;for(int ai:choices[b]){if(sep)cout<<',';sep=true;A op=actions[ai];cout<<'['<<op.w<<','<<op.d<<','<<op.n<<']';}cout<<']';}cout<<"]}"<<endl;
 }}
}
