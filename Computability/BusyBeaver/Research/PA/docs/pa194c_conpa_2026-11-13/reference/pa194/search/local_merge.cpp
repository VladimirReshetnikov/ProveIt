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
struct A{int w,d,n;};
int main(int argc,char**argv){
 if(argc<3)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,MASK=N-1,STEP=argc>3?atoi(argv[3]):100;
 map<int,array<A,2>> rows;int q,b,w,n;char d;
 string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};}
 map<int,vector<bool>> reached;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!rows.count(q))return;if(!reached.count(q))reached[q]=vector<bool>(N);if(!reached[q][p]){reached[q][p]=true;todo.emplace(q,p);}};
 for(int p=0;p<N;p++)add(74,p);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
  if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 if(argc>4){ifstream pin(argv[4]);map<int,vector<bool>> supplied;int rq,rp;while(pin>>rq>>rp){if(!supplied.count(rq))supplied[rq]=vector<bool>(N);supplied[rq][rp]=true;}for(auto const&[rq,bits]:supplied)reached[rq]=bits;}
 vector<int>states;map<int,vector<int>>patterns;
 for(auto const&[q,a]:rows){states.push_back(q);for(int p=0;p<N;p++)if(reached[q][p])patterns[q].push_back(p);}
 cerr<<"states "<<states.size()<<" K "<<K<<" pairs "<<states.size()*states.size()<<endl;
 for(int a:states){if(a==74)continue;for(int r:states){if(a==r)continue;bool ok=true;int longest=0;
  for(int p:patterns[a]){int bit=p>>K&1;A old=rows[a][bit];int target=old.n==a?r:old.n;int targetp=(p&~(1<<K))|(old.w<<K);
   int c=r,h=0,t=p;bool hit=false;
   for(int st=0;st<=STEP;st++){
    if(st&&c==target&&h==old.d&&t==targetp){hit=true;longest=max(longest,st);break;}
    if(h < -K||h>K||!rows.count(c))break;
    A op=rows[c][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n==a?r:op.n;
   }if(!hit){ok=false;break;}
  }if(ok)cout<<"MERGE "<<a<<" -> "<<r<<" contexts "<<patterns[a].size()<<" max_steps "<<longest<<endl;
 }}
}
