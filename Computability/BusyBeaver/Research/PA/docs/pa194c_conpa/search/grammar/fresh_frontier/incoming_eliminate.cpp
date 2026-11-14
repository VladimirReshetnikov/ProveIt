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
using namespace std;
struct A{int w,d,n;};struct Good{bitset<2500>v;int steps;};
int main(int argc,char**argv){
 if(argc<3)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,MASK=N-1,STEP=argc>3?atoi(argv[3]):30;
 A rows[2500][2];bool exists[2500]={};int q,b,w,n;char d;vector<int>states;
 string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};if(!exists[q])states.push_back(q);exists[q]=true;}
 map<int,vector<bool>> reached;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!exists[q])return;if(!reached.count(q))reached[q]=vector<bool>(N);if(!reached[q][p]){reached[q][p]=true;todo.emplace(q,p);}};
 for(int p=0;p<N;p++)add(74,p);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
  if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 if(argc>4){ifstream pin(argv[4]);map<int,vector<bool>> supplied;int rq,rp;while(pin>>rq>>rp){if(!supplied.count(rq))supplied[rq]=vector<bool>(N);supplied[rq][rp]=true;}for(auto const&[rq,bits]:supplied)reached[rq]=bits;}
 map<int,array<vector<int>,2>>patterns;for(int q:states)for(int p=0;p<N;p++)if(reached[q][p])patterns[q][p>>K&1].push_back(p);

 vector<A>actions;for(int n:states)for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,n});
 for(int removed:states){
  if(removed==74||rows[removed][0].n==removed||rows[removed][1].n==removed)continue;
  vector<pair<int,int>> incoming;
  bool edited[2500][2]={};
  for(int q:states)for(int b=0;b<2;b++)if(rows[q][b].n==removed){incoming.emplace_back(q,b);edited[q][b]=true;}
  if(incoming.empty())continue;
  vector<vector<int>> choices;
  bool complete=true;
  for(auto [q,b]:incoming){
   A old=rows[q][b];vector<int>good;
   for(int ai=0;ai<(int)actions.size();ai++){
    A first=actions[ai];if(first.n==removed)continue;bool okay=true;
    for(int p:patterns[q][b]){
     int tp=(p&~(1<<K))|(old.w<<K);int th=old.d;
     A old2=rows[removed][tp>>(th+K)&1];tp=(tp&~(1<<(th+K)))|(old2.w<<(th+K));th+=old2.d;
     int tn=old2.n;
     int c=first.n,h=first.d,t=(p&~(1<<K))|(first.w<<K);bool hit=false;
     for(int st=1;st<=STEP;st++){
      if(c==tn&&h==th&&t==tp){hit=true;break;}
      if(c==removed||h < -K||h>K||c<0||c>=2500||!exists[c])break;
      int cb=t>>(h+K)&1;if(edited[c][cb])break;
      A op=rows[c][cb];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
     }if(!hit){okay=false;break;}
    }
    if(okay)good.push_back(ai);
   }
   if(good.empty()){complete=false;break;}choices.push_back(good);
  }
  cerr<<"REM "<<removed<<" inputs "<<incoming.size()<<" solved "<<choices.size()<<endl;
  if(!complete)continue;
  cout<<"{\"removed\":"<<removed<<",\"patches\":[";
  for(int i=0;i<(int)incoming.size();i++){
   if(i)cout<<',';auto[q,b]=incoming[i];cout<<"{\"q\":"<<q<<",\"b\":"<<b<<",\"actions\":[";
   bool sep=false;for(int ai:choices[i]){if(sep)cout<<',';sep=true;A op=actions[ai];cout<<'['<<op.w<<','<<op.d<<','<<op.n<<']';}cout<<"]}";
  }cout<<"]}"<<endl;
 }
}
