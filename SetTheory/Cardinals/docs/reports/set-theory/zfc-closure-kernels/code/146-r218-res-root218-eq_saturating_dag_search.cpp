// Conditional source discovery: right-child CD has saturating fallthrough.
// No literal machine implementation is assumed by this search.
#include <bits/stdc++.h>
using namespace std;
using Sig=vector<short>;
struct Node {Sig s; int a=-1,b=-1,cost=0; bool right_cd=false;};
struct Hash {size_t operator()(Sig const&v)const{size_t h=1469598103934665603ull;for(short x:v)h=(h^(x+2))*1099511628211ull;return h;}};
int M,W,N,na; long long trials=0,hits=0;
int compose_at(Sig const&a,Sig const&b,int v,bool satb=false){
  int cur=v,e=-1; unsigned char seen[121]={};
  while(!seen[cur]) {
    seen[cur]=1;e=a[cur];if(e<0)return -1;
    int k=e%16,st=e/16;
    if(k)return k<8?e-1:e;
    e=b[st];if(e<0)return -1;k=e%16;st=e/16;
    if(satb && k==1){k=0;e--;}
    if(k==9){cur=st;continue;}return k>9?e-1:e;
  }return -1;
}
bool goal_pair(Sig const&a,Sig const&b,bool satb=false){
  for(int x=0;x<5;x++)for(int y=0;y<5;y++)
    if(compose_at(a,b,x*W+y,satb)!=(x==y?0:1))return false;
  return true;
}
Sig compose(Sig const&a,Sig const&b,bool satb=false){Sig s(N);for(int v=0;v<N;v++)s[v]=compose_at(a,b,v,satb);return s;}
string repr(vector<Node>const&g,int id,string const&shared=""){
  if(id<na)return to_string(id);
  if(id==na && !shared.empty())return shared;
  return "["+repr(g,g[id].a,shared)+","+repr(g,g[id].b,shared)+"]";
}
int main(int argc,char**argv){
  if(argc<3)return 2;ifstream in(argv[1]);ofstream out(argv[2]);in>>M>>na;W=M+1;N=W*W;
  if(N>121||na<14)return 3;
  bool left_only=argc>3 && string(argv[3])=="left";int budget=argc>4?atoi(argv[4]):5;
  vector<Node> base;
  for(int a=0;a<na;a++){Node n;n.s.resize(N);for(auto&x:n.s)in>>x;base.push_back(n);}
  vector<Node> pool=base;vector<vector<int>> layers(4);unordered_map<Sig,int,Hash> idx;
  for(int i=0;i<na;i++)if(idx.emplace(pool[i].s,i).second)layers[0].push_back(i);
  for(int c=1;c<=3;c++){
    for(int ca=0;ca<c;ca++)for(int a:layers[ca])for(int b:layers[c-1-ca]){
      bool bad=pool[a].right_cd||pool[b].right_cd||b==4||b==5;
      if(left_only&&bad)continue;
      Sig s=compose(pool[a].s,pool[b].s,b==4||b==5);if(idx.count(s))continue;
      int id=pool.size();pool.push_back({move(s),a,b,c,bad});idx[pool.back().s]=id;layers[c].push_back(id);
    }
    cout<<"POOL "<<c<<" "<<layers[c].size()<<endl;
  }
  long long attempted=0;set<string> unique_hits;
  for(int candidate=na;candidate<(int)pool.size();candidate++){
    int maxcost=budget-pool[candidate].cost;if(maxcost<1)continue;
    vector<Node> g=base;g.push_back({pool[candidate].s,-1,-1,0,pool[candidate].right_cd});
    vector<vector<int>> ls(maxcost+1);unordered_map<Sig,int,Hash> ix;
    for(int i=0;i<(int)g.size();i++)if(ix.emplace(g[i].s,i).second)ls[0].push_back(i);
    for(int c=1;c<=maxcost;c++){
      for(int ca=0;ca<c;ca++)for(int a:ls[ca])for(int b:ls[c-1-ca]){
        bool bad=g[a].right_cd||g[b].right_cd||b==4||b==5;
        if(left_only&&bad)continue;trials++;
        bool goal=goal_pair(g[a].s,g[b].s,b==4||b==5);
        if(goal){
          string shared=repr(pool,candidate),tr="["+repr(g,a,shared)+","+repr(g,b,shared)+"]";
          if(unique_hits.insert(tr).second){hits++;out<<tr<<"\n";out.flush();cout<<"HIT "<<hits<<" shared "<<candidate<<" sharedcost "<<pool[candidate].cost<<" rootcost "<<c<<" rightcd "<<bad<<endl;}
        }
        if(c==maxcost)continue;
        Sig s=compose(g[a].s,g[b].s,b==4||b==5);if(ix.count(s))continue;
        int id=g.size();g.push_back({move(s),a,b,c,bad});ix[g.back().s]=id;ls[c].push_back(id);
      }
    }
    attempted++;
    if(attempted%100==0)cout<<"SHARED "<<attempted<<"/"<<pool.size()-na<<" trials "<<trials<<" hits "<<hits<<endl;
  }
  cout<<"DONE shared "<<attempted<<" trials "<<trials<<" hits "<<hits<<" budget "<<budget<<" left_only "<<left_only<<endl;
}
