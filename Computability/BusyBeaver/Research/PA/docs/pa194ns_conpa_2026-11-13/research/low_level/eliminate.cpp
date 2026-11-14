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
struct A{int w,d,n;};struct C{int q,h,p;};
int main(int argc,char**argv){
 if(argc<3)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,MASK=N-1,STEP=argc>3?atoi(argv[3]):40;
 A rows[2500][2];bool exists[2500]={};int q,b,w,n;char d;vector<int>states;
 string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};if(!exists[q])states.push_back(q);exists[q]=true;}
 map<int,vector<bool>> reached;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!exists[q])return;if(!reached.count(q))reached[q]=vector<bool>(N);if(!reached[q][p]){reached[q][p]=true;todo.emplace(q,p);}};
 for(int p=0;p<N;p++)add(74,p);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
  if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 if(argc>4){ifstream pin(argv[4]);map<int,vector<bool>> supplied;int rq,rp;while(pin>>rq>>rp){if(!supplied.count(rq))supplied[rq]=vector<bool>(N);supplied[rq][rp]=true;}for(auto const&[rq,bits]:supplied)reached[rq]=bits;}
 map<int,array<vector<int>,2>>patterns;for(int q:states)for(int p=0;p<N;p++)if(reached[q][p])patterns[q][p>>K&1].push_back(p);
 vector<A>actions;for(int w=0;w<2;w++)for(int d:{-1,1})for(int n:states)actions.push_back({w,d,n});
 for(int rem:states){if(rem==74)continue;
 vector<pair<int,int>> incoming;bool forbid[2500][2]={};
 for(int q:states)for(int b=0;b<2;b++)if(rows[q][b].n==rem&&q!=rem){incoming.push_back({q,b});forbid[q][b]=true;}
 vector<vector<A>> solutions; bool all=true;
 for(auto [q,b]:incoming){A old=rows[q][b];vector<A> choices;
 // Precompute every old future in the fixed untouched window.
 vector<vector<C>> futures;
 for(int p:patterns[q][b]){vector<C> future;int oq=old.n,oh=old.d,ot=(p&~(1<<K))|(old.w<<K);
  for(int st=1;st<=STEP;st++){
   if(oq!=rem)future.push_back({oq,oh,ot});
   if(oh < -K||oh>K||oq<0||oq>=2500||!exists[oq])break;
   A op=rows[oq][ot>>(oh+K)&1];ot=(ot&~(1<<(oh+K)))|(op.w<<(oh+K));oh+=op.d;oq=op.n;
  }futures.push_back(future);
 }
 for(A first:actions){if(first.n==rem)continue;bool good=true;
  int pi=0;for(int p:patterns[q][b]){int c=first.n,h=first.d,t=(p&~(1<<K))|(first.w<<K);bool hit=false;
   for(int st=1;st<=STEP;st++){
    for(C end:futures[pi])if(c==end.q&&h==end.h&&t==end.p){hit=true;break;}
    if(hit)break;
    if(c==rem||h < -K||h>K||c<0||c>=2500||!exists[c])break;
    int bit=t>>(h+K)&1;if(forbid[c][bit])break;
    A op=rows[c][bit];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
   }
   if(!hit){good=false;break;}pi++;
  }
  if(good)choices.push_back(first);
 }
 if(choices.empty()){all=false;break;}solutions.push_back(choices);
 }
 if(all){cout<<"{\"remove\":"<<rem<<",\"rewrites\":[";bool sep=false;for(int j=0;j<(int)incoming.size();j++){auto[q,b]=incoming[j];if(sep)cout<<',';sep=true;cout<<"{\"q\":"<<q<<",\"b\":"<<b<<",\"choices\":[";bool first=true;for(A a:solutions[j]){if(!first)cout<<',';first=false;cout<<'['<<a.w<<','<<a.d<<','<<a.n<<']';}cout<<"]}";}cout<<"]}"<<endl;}
 cerr<<"STATE "<<rem<<" INCOMING "<<incoming.size()<<" SOLVED "<<solutions.size()<<endl;
 }
}
