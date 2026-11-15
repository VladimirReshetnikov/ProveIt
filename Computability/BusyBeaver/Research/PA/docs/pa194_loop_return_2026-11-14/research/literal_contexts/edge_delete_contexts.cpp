// Adapted from pinned LC incoming_edge_search/edge_delete.cpp.
// Changes: accept explicit source/literal-context envelope as argv[6];
// include the actual terminal label as a possible replacement successor.
#include <iostream>
#include <fstream>
#include <sstream>
#include <array>
#include <map>
#include <vector>
#include <queue>
#include <algorithm>
#include <cstdlib>
using namespace std;
struct A{int w,d,n;};struct C{int q,h,t;};
int main(int argc,char**argv){
 if(argc<3)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,MASK=N-1,STEP=argc>3?atoi(argv[3]):80,START=argc>4?atoi(argv[4]):74,OLD=argc>5?atoi(argv[5]):12;
 A rows[5000][2];bool exists[5000]={};int q,b,w,n;char d;vector<int>states;
 string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};if(!exists[q])states.push_back(q);exists[q]=true;}
 map<int,vector<bool>>reached;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!exists[q])return;if(!reached.count(q))reached[q]=vector<bool>(N);if(!reached[q][p]){reached[q][p]=true;todo.emplace(q,p);}};
 add(START,0);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
  if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 map<int,array<vector<int>,2>>patterns;for(int q:states)for(int p=0;p<N;p++)if(reached[q][p])patterns[q][p>>K&1].push_back(p);
 if(argc>6){patterns.clear();ifstream pf(argv[6]);int q,p;while(pf>>q>>p)patterns[q][p>>K&1].push_back(p);}
 vector<int> alltargets=states;for(int q:states)for(int b:{0,1})if(!exists[rows[q][b].n]&&find(alltargets.begin(),alltargets.end(),rows[q][b].n)==alltargets.end())alltargets.push_back(rows[q][b].n);
 vector<A>actions;for(int n:alltargets)for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,n});
 auto apply=[&](C c,A a){return C{a.n,c.h+a.d,(c.t&~(1<<(c.h+K)))|(a.w<<(c.h+K))};};
 for(int del:states){if(del==START)continue;
  vector<pair<int,int>> incoming;bool touched[5000][2]={};
  for(int p:states)for(int b=0;b<2;b++)if(p!=del&&rows[p][b].n==del){incoming.emplace_back(p,b);touched[p][b]=true;}
  vector<vector<int>> good;bool okay=true;
  for(auto[p,b]:incoming){
   vector<vector<C>> targets;targets.reserve(patterns[p][b].size());
   for(int t:patterns[p][b]){
    C c=apply({p,0,t},rows[p][b]); vector<C> ts;
    for(int s=1;s<=OLD;s++){
      if(c.q!=del)ts.push_back(c);
      if(c.h < -K||c.h>K||!exists[c.q])break;
      c=apply(c,rows[c.q][c.t>>(c.h+K)&1]);
    }
    if(ts.empty()){okay=false;break;}targets.push_back(ts);
   }
   if(!okay)break;
   vector<int> choices;
   for(int ai=0;ai<(int)actions.size();ai++){A first=actions[ai];if(first.n==del)continue;bool valid=true;
    for(int i=0;i<(int)targets.size();i++){
     C c=apply({p,0,patterns[p][b][i]},first);bool hit=false;
     for(int s=1;s<=STEP;s++){
      for(C expect:targets[i])if(c.q==expect.q&&c.h==expect.h&&c.t==expect.t){hit=true;break;} if(hit)break;
      if(c.q==del||c.h < -K||c.h>K||!exists[c.q])break;
      int read=c.t>>(c.h+K)&1;if(touched[c.q][read])break;
      c=apply(c,rows[c.q][read]);
     }
     if(!hit){valid=false;break;}
    }
    if(valid)choices.push_back(ai);
   }
   if(choices.empty()){okay=false;break;}good.push_back(choices);
  }
  cerr<<"Q "<<del<<" in "<<incoming.size()<<" solved "<<good.size()<<"\n";
  if(!okay)continue;
  cout<<"{\"remove\":"<<del<<",\"replacements\":[";
  for(int i=0;i<(int)incoming.size();i++){if(i)cout<<",";cout<<"{\"row\":["<<incoming[i].first<<","<<incoming[i].second<<"],\"choices\":[";
   for(int j=0;j<(int)good[i].size();j++){if(j)cout<<",";A a=actions[good[i][j]];cout<<"["<<a.w<<","<<a.d<<","<<a.n<<"]";}cout<<"]}";
  }cout<<"]}"<<endl;
 }
}
