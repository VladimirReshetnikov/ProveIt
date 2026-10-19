// Search direct two-row folds after changing how controls are entered.
// Uses a finite inductive window overapproximation from every tape at state95.
// This discovery program emits candidates; an independent checker is required.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <queue>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Row {int w,d,z;};
struct Conf {int q,h,m;};
struct Case {int m;vector<Conf> goals;};
Row tab[256][2];vector<int> states,dom[256];
vector<Case> pre[256][2],cs[2];
int R=5,W,F,CAP=65,retained,deleted;
long long tests=0;
int mapped(int q){return q==deleted?retained:q;}
bool check(int b,const Row rows[2],bool full){
 for(const Case& c:cs[b]){
  ++tests;int q=retained,h=0,m=c.m;bool ok=false;
  for(int k=0;k<CAP;++k){
   if(abs(h)>R||q==254)break;
   int bit=(m>>(R+h))&1;
   if(q==retained&&bit!=b&&!full){ok=true;break;}
   Row a=q==retained?rows[bit]:tab[q][bit];
   m=(m&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;q=mapped(a.z);
   for(const Conf& g:c.goals)if(q==mapped(g.q)&&h==g.h&&m==g.m){ok=true;break;}
   if(ok)break;
  }
  if(!ok)return false;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc<2)return 2;
 if(argc>2)R=stoi(argv[2]);
 if(argc>3)CAP=stoi(argv[3]);
 int focus=argc>4?stoi(argv[4]):-1;
 W=2*R+1;F=(1<<W)-1;
 ifstream f(argv[1]);string line;set<int> present;
 while(getline(f,line)){
  if(line.empty()||line[0]=='#')continue;
  istringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;
  tab[q][b]={w,d=='R'?1:-1,z};present.insert(q);
 }
 states.assign(present.begin(),present.end());
 vector<vector<bool>>seen(256,vector<bool>(F+1));queue<pair<int,int>>todo;
 for(int m=0;m<=F;++m){seen[95][m]=true;todo.push({95,m});}
 while(!todo.empty()){
  auto [q,m]=todo.front();todo.pop();dom[q].push_back(m);if(q==254)continue;
  Row a=tab[q][(m>>R)&1];int x=(m&~(1<<R))|(a.w<<R);
  int low=a.d==1?x>>1:(x<<1)&F;
  int high=low|(a.d==1?1<<(W-1):1);
  for(int y:{low,high})if(!seen[a.z][y]){seen[a.z][y]=true;todo.push({a.z,y});}
 }
 long long contexts=0;
 for(int q:states){
  sort(dom[q].begin(),dom[q].end(),[&](int a,int b){return ((a*101)&F)<((b*101)&F);});
  for(int m:dom[q]){
   int bit=(m>>R)&1;Case c{m,{}};int s=q,h=0,t=m;
   for(int k=0;k<CAP;++k){
    if(abs(h)>R||s==254)break;
    Row a=tab[s][(t>>(R+h))&1];t=(t&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;s=a.z;
    c.goals.push_back({s,h,t});
   }
   pre[q][bit].push_back(move(c));++contexts;
  }
 }
 cerr<<"contexts "<<contexts<<" focus_domain "<<(focus>=0?dom[focus].size():0)<<endl;
 long long pairs=0,rowchecks=0,candidates=0;auto started=chrono::steady_clock::now();
 for(int p:states)for(int q:states)if(p<q&&(focus<0||p==focus||q==focus)){
  retained=p;deleted=q;
  if(q==95)continue;
  for(int b=0;b<2;++b){
   cs[b].clear();for(int s:{p,q})cs[b].insert(cs[b].end(),pre[s][b].begin(),pre[s][b].end());
   stable_sort(cs[b].begin(),cs[b].end(),[&](const Case&a,const Case&b){return ((a.m*101)&F)<((b.m*101)&F);});
  }
  vector<Row> good[2];Row rows[2];
  for(int b=0;b<2;++b){
   for(int w=0;w<2;++w)for(int d:{-1,1})for(int z:states)if(z!=q){
    rows[b]={w,d,z};++rowchecks;if(check(b,rows,false))good[b].push_back(rows[b]);
   }
   if(good[b].empty())break;
  }
  for(Row a:good[0])for(Row b:good[1]){
   rows[0]=a;rows[1]=b;
   if(check(0,rows,true)&&check(1,rows,true)){
    cout<<"FOLD "<<p<<' '<<q<<' '<<a.w<<' '<<a.d<<' '<<a.z<<' '<<b.w<<' '<<b.d<<' '<<b.z<<endl;++candidates;
   }
  }
  ++pairs;
 }
 cerr<<"FINISHED pairs "<<pairs<<" rowchecks "<<rowchecks<<" contexttests "<<tests<<" candidates "<<candidates<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}
