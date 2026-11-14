#include <iostream>
#include <fstream>
#include <sstream>
#include <array>
#include <map>
#include <set>
#include <vector>
#include <queue>
#include <algorithm>
#include <cstdlib>
using namespace std;
struct A{int w,d,n;};
int main(int argc,char**argv){
 if(argc<3)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,MASK=N-1,STEP=argc>3?atoi(argv[3]):100;
 map<int,array<A,2>> rows;int q,b,w,n;char d;string line;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};}
 map<int,vector<bool>> reached;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!rows.count(q))return;if(!reached.count(q))reached[q]=vector<bool>(N);if(!reached[q][p]){reached[q][p]=true;todo.emplace(q,p);}};
 for(int p=0;p<N;p++)add(74,p);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
 if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 if(argc>4){ifstream pin(argv[4]);map<int,vector<bool>>supplied;int rq,rp;while(pin>>rq>>rp){if(!supplied.count(rq))supplied[rq]=vector<bool>(N);supplied[rq][rp]=true;}for(auto const&[rq,bits]:supplied)reached[rq]=bits;}
 vector<int>states;map<int,array<vector<int>,2>>patterns;
 for(auto const&[q,a]:rows){states.push_back(q);for(int p=0;p<N;p++)if(reached[q][p])patterns[q][p>>K&1].push_back(p);}
 vector<A>actions;for(int n:states)for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,n});
 for(int a:states){if(a==74||rows[a][0].n==a||rows[a][1].n==a)continue;
  vector<pair<int,int>> incoming;for(int p:states)for(int bt=0;bt<2;bt++)if(rows[p][bt].n==a)incoming.push_back({p,bt});
  if(incoming.empty())continue;
  set<pair<int,int>> avoid(incoming.begin(),incoming.end());
  bool okay=true;vector<vector<A>>allchoices;
  for(auto [p,bt]:incoming){vector<A>choices;A old=rows[p][bt];
   for(A first:actions){if(first.n==a)continue;bool good=true;int maxst=0;
    for(int pat:patterns[p][bt]){
     int et=(pat&~(1<<K))|(old.w<<K);int eh=old.d;
     A second=rows[a][et>>(eh+K)&1];et=(et&~(1<<(eh+K)))|(second.w<<(eh+K));eh+=second.d;int en=second.n;
     int c=first.n,h=first.d,t=(pat&~(1<<K))|(first.w<<K);bool hit=false;
     for(int st=1;st<=STEP;st++){
      if(c==en&&h==eh&&t==et){hit=true;maxst=max(maxst,st);break;}
      if(c==a||h < -K||h>K||!rows.count(c))break;
      int read=t>>(h+K)&1;if(avoid.count({c,read}))break;
      A op=rows[c][read];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
     }if(!hit){good=false;break;}
    }
    if(good)choices.push_back(first);
   }
   if(choices.empty()){okay=false;break;}allchoices.push_back(choices);
  }
  if(okay){cout<<"{\"remove\":"<<a<<",\"rewrites\":[";for(size_t i=0;i<incoming.size();i++){if(i)cout<<',';cout<<"{\"row\":["<<incoming[i].first<<','<<incoming[i].second<<"],\"actions\":[";bool sep=false;for(A act:allchoices[i]){if(sep)cout<<',';sep=true;cout<<'['<<act.w<<','<<act.d<<','<<act.n<<']';}cout<<"]}";}cout<<"]}"<<endl;}
  cerr<<a<<" "<<(okay?"FOUND":"no")<<endl;
 }
}
