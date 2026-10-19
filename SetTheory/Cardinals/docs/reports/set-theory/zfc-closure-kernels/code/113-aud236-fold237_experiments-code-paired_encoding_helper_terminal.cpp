// Terminal-observation variant: target254 is allowed; all halted endpoints are related.
// Search simultaneous caller-cell encodings for BOTH states of a fold.
// A state s is represented by the retained label, a head offset in {0,-2*d_s},
// and one of four Boolean maps (identity,0,1,negation) on cell h-d_s.
// This permits paired encodings beyond the earlier identity-on-retained search.
// Empirical profiles only establish bounded discovery evidence.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <tuple>
#include <vector>
using namespace std;
struct Row {int w,d,z;bool operator==(Row const&a)const{return tie(w,d,z)==tie(a.w,a.d,a.z);}};
struct Cfg{int q,h,t;};struct Case{int q,t;vector<Cfg>goals;};
struct Encoding {int mode,shift,tag;};
array<array<Row,2>,256>T;vector<int>states,inv[256];vector<Case>pre[256];
vector<Case const*>cs[2];int L=5,R=5,H=33,W,N,mask,p,q;
struct Patch{int edge;Row a;};vector<Patch>patches;vector<int>byedge[512];int helper=-1;vector<int>failededges;long long helpertrials=0;
Encoding E[256];Row rr[2];long long tests=0,trials=0,partial=0,full=0,found=0;
int fmap(int b,int m){return m==0?b:m==1?0:m==2?1:1-b;}
int encode(int tape,int pos,int mode){int bit=tape>>(L+pos)&1;return (tape&~(1<<(L+pos)))|(fmap(bit,mode)<<(L+pos));}
bool check(Case const&c,int b,bool complete,bool save=false){
 ++tests;int s=c.q,h=0,t=c.t;vector<int>used;if(c.q==p||c.q==q){auto e=E[c.q];s=p;h=e.shift;t=encode(c.t,e.tag,e.mode);}
 for(int step=0;step<H;step++){
  if(h < -L||h>R||s==254)break;
  int bit=t>>(L+h)&1;if(!complete&&s==p&&bit!=b)return true;
  Row a;
  if(s==p)a=rr[bit];else{int edge=2*s+bit;if(save)used.push_back(edge);a=helper>=0&&patches[helper].edge==edge?patches[helper].a:T[s][bit];if(a.z==p||a.z==q){auto ez=E[a.z];a.w=fmap(a.w,ez.mode);a.d+=ez.shift;a.z=p;}}
  t=(t&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;s=a.z;
  for(auto const&g:c.goals){int gh=g.h,gt=g.t,gs=g.q;
   if(gs==p||gs==q){auto eg=E[gs];int pos=gh+eg.tag;if(pos < -L||pos>R)continue;gh+=eg.shift;gt=encode(gt,pos,eg.mode);gs=p;}
   if(s==254&&gs==254)return true;
   if(s==gs&&h==gh&&t==gt)return true;
  }
 }
 if(save){sort(used.begin(),used.end());used.erase(unique(used.begin(),used.end()),used.end());failededges=move(used);}
 return false;
}
bool checkset(int b,bool complete,bool save=false){for(auto c:cs[b])if(!check(*c,b,complete,save))return false;return true;}
int main(int argc,char**argv){
 if(argc<2)return 2;if(argc>2)L=stoi(argv[2]);if(argc>3)R=stoi(argv[3]);if(argc>4)H=stoi(argv[4]);
 if(argc<7){cerr<<"need neutral patch file at argv6"<<endl;return 2;}
 ifstream pf(argv[6]);int pq,pb,pw,pd,pz,plen;while(pf>>pq>>pb>>pw>>pd>>pz>>plen){int id=patches.size();patches.push_back({2*pq+pb,{pw,pd,pz}});byedge[2*pq+pb].push_back(id);}
 bool similaronly=argc>7?stoi(argv[7]):true;int typefirst=argc>8?stoi(argv[8]):1;
 int firstp=argc>9?stoi(argv[9]):0,lastp=argc>10?stoi(argv[10]):256;
 W=L+R+1;N=1<<W;mask=N-1;ifstream f(argv[1]);string line;set<int>exist;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int s,b,w,z;char d;ss>>s>>b>>w>>d>>z;T[s][b]={w,d=='R'?1:-1,z};exist.insert(s);}states.assign(exist.begin(),exist.end());vector<int>targets=states;targets.push_back(254);
 bool empirical=argc>5&&string(argv[5])!="-";
 if(empirical){ifstream fp(argv[5]);int s,t;while(fp>>s>>t)inv[s].push_back(t);}
 else{vector<vector<bool>>seen(256,vector<bool>(N));queue<pair<int,int>>todo;for(int t=0;t<N;t++){seen[95][t]=true;todo.push({95,t});}
  while(!todo.empty()){auto[s,t]=todo.front();todo.pop();inv[s].push_back(t);if(s==254)continue;auto a=T[s][t>>L&1];int u=(t&~(1<<L))|(a.w<<L),u0,u1;
   if(a.d==1){u0=u>>1;u1=u0|(1<<(W-1));}else{u0=(u<<1)&mask;u1=u0|1;}for(int v:{u0,u1})if(!seen[a.z][v]){seen[a.z][v]=true;todo.push({a.z,v});}
  }
 }
 long long contexts=0;for(int s:states){sort(inv[s].begin(),inv[s].end(),[&](int x,int y){return (x*101&mask)<(y*101&mask);});for(int t:inv[s]){Case c{s,t,{}};int z=s,h=0,u=t;
   for(int k=0;k<H;k++){if(z==254||h < -L||h>R)break;auto a=T[z][u>>(L+h)&1];u=(u&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;z=a.z;c.goals.push_back({z,h,u});}pre[s].push_back(move(c));contexts++;}
 }
 auto start=chrono::steady_clock::now();int pairs=0,variants=0;
 cerr<<"BEGIN paired caller encoding contexts "<<contexts<<" radius "<<L<<' '<<R<<" H "<<H<<" empirical "<<empirical<<" similar "<<similaronly<<" typefirst "<<typefirst<<endl;
 for(int pp:states)if(pp!=95&&pp>=firstp&&pp<lastp)for(int qq:states)if(pp<qq&&qq!=95){
  if(pp!=77&&qq!=77)continue;
  if(similaronly&&!(T[pp][0]==T[qq][0])&&!(T[pp][1]==T[qq][1]))continue;p=pp;q=qq;
  int ds[2];bool valid=true;for(int i=0;i<2;i++){int z=i?q:p;set<int>directions;for(int s:states)if(s!=p&&s!=q)for(auto a:T[s])if(a.z==z)directions.insert(a.d);if(directions.size()!=1){valid=false;break;}ds[i]=*directions.begin();}
  if(!valid)continue;
  for(int tp=typefirst;tp<8;tp++)for(int tq=typefirst;tq<8;tq++){
   E[p]={tp%4,tp>=4?-2*ds[0]:0,-ds[0]};E[q]={tq%4,tq>=4?-2*ds[1]:0,-ds[1]};cs[0].clear();cs[1].clear();
   for(int s:{p,q})for(auto const&c:pre[s]){int bit=c.t>>(L+E[s].shift)&1;cs[bit].push_back(&c);}
   for(int b=0;b<2;b++)stable_sort(cs[b].begin(),cs[b].end(),[&](auto x,auto y){return (x->t*101&mask)<(y->t*101&mask);});
   vector<Row>dom[2];map<int,array<vector<Row>,2>> repairs;
   for(int b=0;b<2;b++)for(int w=0;w<2;w++)for(int dir:{-1,1})for(int z:targets)if(z!=q){
    helper=-1;rr[b]={w,dir,z};trials++;
    if(checkset(b,false,true)){dom[b].push_back(rr[b]);partial++;continue;}
    vector<int>options;for(int edge:failededges)if(edge/2!=p&&edge/2!=q)for(int pi:byedge[edge])options.push_back(pi);
    sort(options.begin(),options.end());options.erase(unique(options.begin(),options.end()),options.end());
    for(int pi:options){helper=pi;helpertrials++;if(checkset(b,false))repairs[pi][b].push_back(rr[b]);}
   }
   helper=-1;
   for(auto a:dom[0])for(auto b:dom[1]){
    rr[0]=a;rr[1]=b;full++;
    if(checkset(0,true,true)&&checkset(1,true,true)){
     found++;cout<<"BASE "<<p<<' '<<q<<" ENCODE "<<tp<<' '<<tq<<" DIR "<<ds[0]<<' '<<ds[1]<<" ROWS "<<a.w<<' '<<a.d<<' '<<a.z<<"; "<<b.w<<' '<<b.d<<' '<<b.z<<endl;
    }else for(int edge:failededges)if(edge/2!=p&&edge/2!=q)for(int pi:byedge[edge])repairs[pi];
   }
   for(auto const& kv:repairs){
    helper=kv.first;vector<Row>ok[2];
    for(int b=0;b<2;b++){ok[b]=kv.second[b];for(auto a:dom[b]){rr[b]=a;helpertrials++;if(checkset(b,false))ok[b].push_back(a);}}
    for(auto a:ok[0])for(auto b:ok[1]){
     rr[0]=a;rr[1]=b;full++;if(!checkset(0,true)||!checkset(1,true))continue;
     bool good=true;int edge=patches[helper].edge;
     for(auto const&c:pre[edge/2])if((c.t>>L&1)==edge%2&&!check(c,edge%2,true)){good=false;break;}
     if(!good)continue;found++;auto ha=patches[helper].a;
     cout<<"HELPER "<<edge/2<<' '<<edge%2<<' '<<ha.w<<' '<<ha.d<<' '<<ha.z<<" FOLD "<<p<<' '<<q<<" ENCODE "<<tp<<' '<<tq<<" DIR "<<ds[0]<<' '<<ds[1]<<" ROWS "<<a.w<<' '<<a.d<<' '<<a.z<<"; "<<b.w<<' '<<b.d<<' '<<b.z<<endl;
    }
   }
   helper=-1;variants++;
  }
  pairs++;if(pairs%20==0)cerr<<"PROGRESS pairs "<<pairs<<" last "<<p<<' '<<q<<" variants "<<variants<<" trials "<<trials<<" partial "<<partial<<" full "<<full<<" helpertrials "<<helpertrials<<" tests "<<tests<<" found "<<found<<" sec "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"FINISHED pairs "<<pairs<<" variants "<<variants<<" trials "<<trials<<" partial "<<partial<<" full "<<full<<" helpertrials "<<helpertrials<<" tests "<<tests<<" candidates "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
