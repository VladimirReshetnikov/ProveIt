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
 map<int,array<A,2>> rows;int q,b,w,n;char d;string line;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};}
 map<int,vector<bool>> reached;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!rows.count(q))return;if(!reached.count(q))reached[q]=vector<bool>(N);if(!reached[q][p]){reached[q][p]=true;todo.emplace(q,p);}};
 add(0,0);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
  if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 if(argc>4){ifstream pin(argv[4]);map<int,vector<bool>> supplied;int rq,rp;while(pin>>rq>>rp){if(!supplied.count(rq))supplied[rq]=vector<bool>(N);supplied[rq][rp]=true;}for(auto const&[rq,bits]:supplied)reached[rq]=bits;}
 vector<int>states;map<int,vector<int>>patterns;map<int,int>incdirs;
 for(auto const&[q,a]:rows){states.push_back(q);for(auto x:a)incdirs[x.n]|=1<<(x.d+1);for(int p=0;p<N;p++)if(reached.count(q)&&reached[q][p])patterns[q].push_back(p);}

 for(int a:states){if(patterns[a].empty())continue;if(a==0)continue;for(int olddir:{-1,1}){if(incdirs[a] && incdirs[a]!=(1<<(olddir+1)))continue;int mark=-olddir;
 for(bool reverse:{false,true}){int shift=reverse?-2*olddir:0;
 for(int r:states){if(a==r)continue;
 struct Test{int h,t,eq,eh,et;};array<vector<Test>,2>tests;
 for(int src:{a,r})for(int p:patterns[src]){int h=src==a?shift:0,t=src==a?p^(1<<(K+mark)):p;A old=rows[src][(p>>K)&1];int eq=old.n==a?r:old.n,eh=old.d+(old.n==a?shift:0),et=(p&~(1<<K))|(old.w<<K);if(old.n==a)et^=1<<(K+old.d+mark);tests[(t>>(K+h))&1].push_back({h,t,eq,eh,et});}
 array<vector<A>,2>choices;int longest=0;
 for(int bit=0;bit<2;bit++){for(int n:states){if(n==a)continue;for(int w:{0,1})for(int d:{-1,1}){A first{w,d,n};bool good=true;int mx=0;
 for(auto test:tests[bit]){int c=n,h=test.h+d,t=(test.t&~(1<<(K+test.h)))|(w<<(K+test.h));bool hit=false;
 for(int st=1;st<=STEP;st++){
 if(c==test.eq&&h==test.eh&&t==test.et){hit=true;mx=max(mx,st);break;}
 if(c==r||h < -K||h>K||!rows.count(c))break;
 A op=rows[c][(t>>(h+K))&1];if(op.n==a){op.w^=1;if(reverse)op.d=-op.d;op.n=r;}t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
 }if(!hit){good=false;break;}}
 if(good){choices[bit].push_back(first);longest=max(longest,mx);}
 }}if(choices[bit].empty())break;}
 if(!choices[0].empty()&&!choices[1].empty()){cout<<"RETAG-ACTION "<<a<<" -> "<<r<<" offset "<<shift<<" mark "<<mark<<" max_steps "<<longest<<" choices ";for(auto v:choices){cout<<'[';for(auto x:v)cout<<'('<<x.w<<','<<x.d<<','<<x.n<<')';cout<<']';}cout<<endl;}
 }}}}
}
