// Simultaneous head-offset and caller-cell tag conjugacy search.
// For deleted q, F(q,h,t)=(p,h-2d,t xor {h-d}), where d is the common
// direction of external transitions into q. Such callers flip both their
// written bit and movement direction. Both rows of p are synthesized freely.
// Empirical profile mode is discovery only; all-tape mode overapproximates
// arbitrary initial tapes by an inductively closed sliding-window abstraction.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <queue>
#include <set>
#include <sstream>
#include <tuple>
#include <vector>
using namespace std;
struct Row {int w,d,z;};struct Cfg{int q,h,t;};
struct Case{int q,t;vector<Cfg>goals;};
array<array<Row,2>,256>T;vector<int>states,inv[256];vector<Case>pre[256];
vector<Case const*>cs[2];int L=5,R=5,H=33,W,N,mask,p,q,offset,tag;
int tagmode=3, shifted=1;
int encode(int tape,int pos){int bit=(tape>>(L+pos))&1;int val=tagmode==0?bit:tagmode==1?0:tagmode==2?1:1-bit;return (tape&~(1<<(L+pos)))|(val<<(L+pos));}
Row rr[2];long long tests=0,trials=0,partial=0,full=0,found=0;
bool check(Case const&c,int b,bool complete){
 ++tests;int s=p,h=0,t=c.t;
 if(c.q==q){h=offset;t=encode(t,tag);}
 for(int step=0;step<H;step++){
  if(h < -L||h>R||s==254)break;
  int bit=t>>(L+h)&1;
  if(!complete&&s==p&&bit!=b)return true;
  Row a;
  if(s==p)a=rr[bit];
  else {a=T[s][bit];if(a.z==q){a.w=tagmode==0?a.w:tagmode==1?0:tagmode==2?1:1-a.w;if(shifted)a.d=-a.d;a.z=p;}}
  t=(t&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;s=a.z;
  for(auto const&g:c.goals){
   int gh=g.h,gt=g.t,gs=g.q;
   if(gs==q){int pos=gh+tag;if(pos < -L||pos>R)continue;gh+=offset;gt=encode(gt,pos);gs=p;}
   if(s==gs&&h==gh&&t==gt)return true;
  }
 }
 return false;
}
bool checkset(int b,bool complete){for(auto c:cs[b])if(!check(*c,b,complete))return false;return true;}
int main(int argc,char**argv){
 if(argc<2)return 2;if(argc>2)L=stoi(argv[2]);if(argc>3)R=stoi(argv[3]);if(argc>4)H=stoi(argv[4]);
 if(argc>6)tagmode=stoi(argv[6]);if(argc>7)shifted=stoi(argv[7]);
 W=L+R+1;N=1<<W;mask=N-1;ifstream f(argv[1]);string line;set<int>exist;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int s,b,w,z;char d;ss>>s>>b>>w>>d>>z;T[s][b]={w,d=='R'?1:-1,z};exist.insert(s);}states.assign(exist.begin(),exist.end());
 bool empirical=argc>5&&string(argv[5])!="-";
 if(empirical){ifstream fp(argv[5]);int s,t;while(fp>>s>>t)inv[s].push_back(t);}
 else{vector<vector<bool>>seen(256,vector<bool>(N));queue<pair<int,int>>todo;
  for(int t=0;t<N;t++){seen[95][t]=true;todo.push({95,t});}
  while(!todo.empty()){auto[s,t]=todo.front();todo.pop();inv[s].push_back(t);if(s==254)continue;
   auto a=T[s][t>>L&1];int u=(t&~(1<<L))|(a.w<<L),u0,u1;
   if(a.d==1){u0=u>>1;u1=u0|(1<<(W-1));}else{u0=(u<<1)&mask;u1=u0|1;}
   for(int v:{u0,u1})if(!seen[a.z][v]){seen[a.z][v]=true;todo.push({a.z,v});}
  }
 }
 long long contexts=0;
 for(int s:states){sort(inv[s].begin(),inv[s].end(),[&](int x,int y){return (x*101&mask)<(y*101&mask);});
  for(int t:inv[s]){Case c{s,t,{}};int z=s,h=0,u=t;
   for(int k=0;k<H;k++){if(z==254||h < -L||h>R)break;auto a=T[z][u>>(L+h)&1];u=(u&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;z=a.z;c.goals.push_back({z,h,u});}
   pre[s].push_back(move(c));contexts++;
  }
 }
 auto start=chrono::steady_clock::now();int pairs=0,deleted=0;
 cerr<<"BEGIN shifted-tag conjugacy contexts "<<contexts<<" radius "<<L<<' '<<R<<" H "<<H<<" empirical "<<empirical<<" tagmode "<<tagmode<<" shifted "<<shifted<<endl;
 for(int qq:states){if(qq==95)continue;set<int>directions;for(int s:states)if(s!=qq)for(auto a:T[s])if(a.z==qq)directions.insert(a.d);
  if(directions.size()!=1)continue;q=qq;int d=*directions.begin();offset=shifted?-2*d:0;tag=-d;deleted++;
  for(int pp:states)if(pp!=q){p=pp;cs[0].clear();cs[1].clear();
   for(int s:{p,q})for(auto const&c:pre[s]){int bit=c.t>>(L+(s==q?offset:0))&1;cs[bit].push_back(&c);}
   for(int b=0;b<2;b++)stable_sort(cs[b].begin(),cs[b].end(),[&](auto x,auto y){return (x->t*101&mask)<(y->t*101&mask);});
   vector<Row>dom[2];
   for(int b=0;b<2;b++)for(int w=0;w<2;w++)for(int dir:{-1,1})for(int z:states)if(z!=q){rr[b]={w,dir,z};trials++;if(checkset(b,false)){dom[b].push_back(rr[b]);partial++;}}
   for(auto a:dom[0])for(auto b:dom[1]){rr[0]=a;rr[1]=b;full++;if(!checkset(0,true)||!checkset(1,true))continue;found++;
    cout<<"CANDIDATE retained "<<p<<" deleted "<<q<<" shift "<<offset<<" tag "<<tag<<" mode "<<tagmode<<" rows "<<a.w<<' '<<a.d<<' '<<a.z<<"; "<<b.w<<' '<<b.d<<' '<<b.z<<endl;
   }
   pairs++;
  }
  if(deleted%10==0)cerr<<"PROGRESS deleted "<<deleted<<" pairs "<<pairs<<" trials "<<trials<<" partial "<<partial<<" full "<<full<<" tests "<<tests<<" found "<<found<<" sec "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"FINISHED deleted "<<deleted<<" pairs "<<pairs<<" trials "<<trials<<" partial "<<partial<<" full "<<full<<" tests "<<tests<<" candidates "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
