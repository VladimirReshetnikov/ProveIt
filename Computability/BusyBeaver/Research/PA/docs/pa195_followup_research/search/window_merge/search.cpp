#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <tuple>
#include <vector>
using namespace std;
struct Act {int w,d,n; bool operator<(const Act&o) const {return tie(w,d,n)<tie(o.w,o.d,o.n);} bool operator==(const Act&o)const{return tie(w,d,n)==tie(o.w,o.d,o.n);}};
struct Proof {Act act;bitset<4096> used;int maxlen;};
int main(int argc,char**argv){
 if(argc!=2)return 2;ifstream f(argv[1]); int L,R,N,Q;f>>L>>R>>N>>Q;
 map<int,array<Act,2>> rows;vector<int> states, qs;map<int,vector<int>> ctx;
 for(int i=0;i<N;i++){int q;f>>q;states.push_back(q);for(int b=0;b<2;b++){Act a;f>>a.w>>a.d>>a.n;rows[q][b]=a;}}
 for(int i=0;i<Q;i++){int q,k;f>>q>>k;qs.push_back(q);for(int j=0;j<k;j++){int s;f>>s;ctx[q].push_back(s);}}
 vector<Act> actions;states.push_back(254);for(int w=0;w<2;w++)for(int d=0;d<2;d++)for(int n:states)actions.push_back({w,d,n});
 map<pair<int,int>,vector<Proof>> valid;long tested=0,accepted=0;
 for(int q:qs)for(int b=0;b<2;b++){
  vector<int> windows;for(int s:ctx[q])if(((s>>L)&1)==b)windows.push_back(s);
  if(windows.empty()){cerr<<"uncovered "<<q<<" "<<b<<"\n";return 3;}
  Act goal=rows[q][b];
  for(Act a:actions){tested++;bool ok=true;bitset<4096> used;int maxlen=0;
   for(int s:windows){int m=s,h=L,st=q;int gm=(s&~(1<<L))|(goal.w<<L);int gh=L+(goal.d?1:-1),gs=goal.n;Act tr=a;set<tuple<int,int,int>> seen;
    int len=0;
    for(;;){
      len++;m=(m&~(1<<h))|(tr.w<<h);h+=tr.d?1:-1;st=tr.n;
      if(st==gs&&h==gh&&m==gm){maxlen=max(maxlen,len);break;}
      if(h<0||h>=L+R+1||!rows.count(st)||!seen.insert({st,h,m}).second){ok=false;break;}
      used.set(st);tr=rows[st][(m>>h)&1];
    }
    if(!ok)break;
   }
   if(ok){valid[{q,b}].push_back({a,used,maxlen});accepted++;}
  }
 }
 long pairs=0,candidates=0;int bestduration=0;
 for(int a:qs)for(int b:qs)if(a<b){pairs++;array<vector<Act>,2> opts;
  for(int bit=0;bit<2;bit++)for(auto &x:valid[{a,bit}])if(!x.used[a]&&!x.used[b])for(auto &y:valid[{b,bit}])if(x.act==y.act&&!y.used[a]&&!y.used[b]){opts[bit].push_back(x.act);bestduration=max({bestduration,x.maxlen,y.maxlen});}
  if(opts[0].empty()||opts[1].empty())continue;
  for(auto x:opts[0])for(auto y:opts[1]){
   candidates++;
   cout<<"{\"remove\":"<<a<<",\"keep\":"<<b<<",\"actions\":[["<<x.w<<","<<x.d<<","<<x.n<<"],["<<y.w<<","<<y.d<<","<<y.n<<"]]}\n";
  }
 }
 cerr<<"tested_actions "<<tested<<" individually_valid "<<accepted<<" pairs "<<pairs<<" candidates "<<candidates<<" max_local_duration "<<bestduration<<"\n";
}
