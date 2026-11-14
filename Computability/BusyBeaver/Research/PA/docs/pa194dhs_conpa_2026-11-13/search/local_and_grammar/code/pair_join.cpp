// Bounded joining-prefix contraction search. Derived from action_merge.cpp;
// unlike its single-old-transition endpoint, allow a later old endpoint.
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
#include <cstdint>
#include <unordered_set>
using namespace std;
struct A{int w,d,n;};struct Good{bitset<256>v;int steps;};
struct Goal{int q,h,t;bitset<256>v;};
int main(int argc,char**argv){
 if(argc<3)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,MASK=N-1,OLD=argc>3?atoi(argv[3]):40,STEP=argc>4?atoi(argv[4]):120;
 A rows[2500][2];bool exists[2500]={};int ids[2500];int q,b,w,n;char d;vector<int>states;
 string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};if(!exists[q]){ids[q]=states.size();states.push_back(q);}exists[q]=true;}
 if(states.size()>256)return 3;
 map<int,vector<bool>> reached;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!exists[q])return;if(!reached.count(q))reached[q]=vector<bool>(N);if(!reached[q][p]){reached[q][p]=true;todo.emplace(q,p);}};
 add(74,0);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
  if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 map<int,array<vector<int>,2>>patterns;size_t contexts=0;for(int q:states)for(int p=0;p<N;p++)if(reached[q][p]){patterns[q][p>>K&1].push_back(p);contexts++;}
 cerr<<"CONTEXTS "<<contexts<<" WORKING "<<states.size()<<endl;
 map<int,array<map<int,Good>,2>>solutions;
 vector<A>actions;for(int n:states)for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,n});for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,254});
 for(int q:states){for(int b=0;b<2;b++){
  vector<vector<Goal>>goals(patterns[q][b].size());vector<bool>made(goals.size());
  auto getgoals=[&](int j)->const vector<Goal>&{
   if(made[j])return goals[j];made[j]=true;auto &g=goals[j];int c=q,h=0,t=patterns[q][b][j];bitset<256>vis;unordered_set<uint64_t>seen;
   for(int st=1;st<=OLD;st++){
    A op=rows[c][(t>>(h+K))&1];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
    g.push_back({c,h,t,vis});
    if(c==q||h< -K||h>K||c<0||c>=2500||!exists[c])break;
    uint64_t k=(uint64_t(c)<<32)|(uint64_t(h+K)<<24)|uint64_t(t);if(!seen.insert(k).second)break;
    vis[ids[c]]=true;
   }return g;
  };
  for(int ai=0;ai<(int)actions.size();ai++){A first=actions[ai];bool okay=true;bitset<256>vis;int maxsteps=0;
   for(int j=0;j<int(patterns[q][b].size());j++){int p=patterns[q][b][j];auto const&g=getgoals(j);int c=first.n,h=first.d,t=(p&~(1<<K))|(first.w<<K);bool hit=false;bitset<256>pv;
    for(int st=1;st<=STEP;st++){
     for(auto const &goal:g)if(c==goal.q&&h==goal.h&&t==goal.t){hit=true;vis|=pv;vis|=goal.v;maxsteps=max(maxsteps,st);break;}
     if(hit)break;
     if(c==q||h < -K||h>K||c<0||c>=2500||!exists[c])break;
     pv[ids[c]]=true;A op=rows[c][(t>>(h+K))&1];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
    }if(!hit){okay=false;break;}
   }if(okay)solutions[q][b][ai]={vis,maxsteps};
  }
 }cerr<<"Q "<<q<<" choices "<<solutions[q][0].size()<<' '<<solutions[q][1].size()<<endl;}
 for(int a:states){if(a==74||patterns[a][0].empty()&&patterns[a][1].empty())continue;for(int r:states){if(a>=r||r==74||patterns[r][0].empty()&&patterns[r][1].empty())continue;array<vector<int>,2>choices;
  for(int b=0;b<2;b++)for(auto const&[ai,g]:solutions[a][b]){auto it=solutions[r][b].find(ai);if(it!=solutions[r][b].end()&&!g.v[ids[r]]&&!it->second.v[ids[a]])choices[b].push_back(ai);}
  if(choices[0].empty()||choices[1].empty())continue;
  cout<<"{\"remove\":"<<a<<",\"keep\":"<<r<<",\"choices\":[";
  for(int b=0;b<2;b++){if(b)cout<<',';cout<<'[';bool sep=false;for(int ai:choices[b]){if(sep)cout<<',';sep=true;A op=actions[ai];cout<<'['<<op.w<<','<<op.d<<','<<op.n<<']';}cout<<']';}cout<<"]}"<<endl;
 }}
}
