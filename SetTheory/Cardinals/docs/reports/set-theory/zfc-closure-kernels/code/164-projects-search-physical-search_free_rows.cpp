#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <filesystem>
#include <iostream>
#include <map>
#include <set>
#include <tuple>
#include <vector>
using namespace std;
struct Act{int w,d,z;bool operator==(const Act&o)const{return w==o.w&&d==o.d&&z==o.z;}};
struct Config{int q,h,m;bool operator==(const Config&o)const{return q==o.q&&h==o.h&&m==o.m;}};
struct Case{int q,b,m;vector<Config>goals;};
Act T[512][2];vector<int>Q;vector<pair<int,int>>inc[512];vector<int>I[512];
vector<Act>actions;vector<Case>cases;Act rows[2],entryActs[2];bool assigned[2];pair<int,int>entries[2];int keep,drop;long long trials=0,fulls=0,hits=0;chrono::steady_clock::time_point begun;long long limit=240;string output_directory;
bool timed(){return chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-begun).count()>limit;}
Config step(Config c,Act a){return Config{a.z,c.h+a.d,(c.m&~(1<<(c.h+7)))|(a.w<<(c.h+7))};}
int run(const Case&c){
 Config n{c.q,0,c.m};vector<Config>seen;seen.reserve(40);
 for(int tick=0;tick<97;tick++){
  if(n.q==254||n.q==drop||n.h<-7||n.h>7)return -1;
  if(find(seen.begin(),seen.end(),n)!=seen.end())return -1;seen.push_back(n);
  int b=(n.m>>(n.h+7))&1;Act a;
  if(n.q==keep){if(!assigned[b])return b;a=rows[b];}
  else if(pair<int,int>{n.q,b}==entries[0])a=entryActs[0];
  else if(pair<int,int>{n.q,b}==entries[1])a=entryActs[1];
  else {a=T[n.q][b];if(a.z==drop)a.z=keep;}
  n=step(n,a);
  if(find(c.goals.begin(),c.goals.end(),n)!=c.goals.end())return 2;
 }
 return -1;
}
void solve(int ci){
 if((trials&65535)==0&&timed())return;
 for(;ci<(int)cases.size();ci++){
  int status=run(cases[ci]);trials++;
  if(status==-1)return;
  if(status==2)continue;
  assigned[status]=true;
  for(Act a:actions){rows[status]=a;solve(ci);if(timed())break;}
  assigned[status]=false;return;
 }
 hits++;
 cout<<"HIT "<<keep<<' '<<drop<<" entries "<<entries[0].first<<'/'<<entries[0].second<<' '<<entries[1].first<<'/'<<entries[1].second<<" row0 "<<rows[0].w<<' '<<rows[0].d<<' '<<rows[0].z<<" row1 "<<rows[1].w<<' '<<rows[1].d<<' '<<rows[1].z<<" marks "<<entryActs[0].w<<' '<<entryActs[0].d<<' '<<entryActs[1].w<<' '<<entryActs[1].d<<endl;
 ofstream f(output_directory+"/free-rows-hit-"+to_string(hits)+".tm");f<<"#! start 0\n";
 for(int q:Q)if(q!=drop)for(int b=0;b<2;b++){
 Act a=T[q][b];if(a.z==drop)a.z=keep;
 if(q==keep)a=rows[b];else if(pair<int,int>{q,b}==entries[0])a=entryActs[0];else if(pair<int,int>{q,b}==entries[1])a=entryActs[1];
 f<<q<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.z<<'\n';}
}
Case makeCase(int q,int b,int m){Case c{q,b,m,{}};Config a{q,0,m};for(int t=0;t<97;t++){
 if(a.q==254||a.h<-7||a.h>7)break;int x=(a.m>>(a.h+7))&1;a=step(a,T[a.q][x]);if(a.q!=keep&&a.q!=drop)c.goals.push_back(a);
 }return c;}
int main(int argc,char**argv){
 if(argc<3){cerr<<"Usage: search_free_rows DOMAIN_FILE OUTPUT_DIRECTORY [SECONDS]\n";return 2;} output_directory=argv[2];filesystem::create_directories(output_directory);if(argc>3)limit=stoll(argv[3]);ifstream f(argv[1]);if(!f){cerr<<"Cannot open domain file\n";return 2;}int nq;f>>nq;
 for(int i=0;i<nq;i++){int q;f>>q;Q.push_back(q);for(int b=0;b<2;b++){Act&a=T[q][b];f>>a.w>>a.d>>a.z;inc[a.z].push_back({q,b});}}
 for(int i=0;i<nq;i++){int q,n;f>>q>>n;I[q].resize(n);for(int&x:I[q])f>>x;}
 begun=chrono::steady_clock::now();int pairs=0;
 for(int ki=0;ki<nq;ki++)for(int di=ki+1;di<nq;di++){
  keep=Q[ki];drop=Q[di];if(keep==0||drop==0||inc[keep].size()!=1||inc[drop].size()!=1)continue;
  entries[0]=inc[keep][0];entries[1]=inc[drop][0];if(entries[0].first==keep||entries[0].first==drop||entries[1].first==keep||entries[1].first==drop)continue;
  int common=(T[keep][0]==T[drop][0])+(T[keep][1]==T[drop][1]);if(common!=1)continue;
  pairs++;actions.clear();for(int w=0;w<2;w++)for(int d:{-1,1}){for(int z:Q)if(z!=drop)actions.push_back({w,d,z});actions.push_back({w,d,254});}
  vector<Case>first,rest;
  for(auto [q,b]:entries){vector<int>masks;for(int m:I[q])if(((m>>7)&1)==b)masks.push_back(m);
   set<int>chosen;for(int i:{0,(int)masks.size()-1,(int)masks.size()/2,(int)masks.size()/4,3*(int)masks.size()/4})if(chosen.insert(i).second)first.push_back(makeCase(q,b,masks[i]));
   for(int i=0;i<(int)masks.size();i++)if(!chosen.count(i))rest.push_back(makeCase(q,b,masks[i]));
  }
  cases=first;cases.insert(cases.end(),rest.begin(),rest.end());
  for(int w0=0;w0<2;w0++)for(int d0:{-1,1})for(int w1=0;w1<2;w1++)for(int d1:{-1,1}){
   entryActs[0]={w0,d0,keep};entryActs[1]={w1,d1,keep};assigned[0]=assigned[1]=false;solve(0);if(timed())goto done;
  }
  cout<<"PAIR "<<pairs<<' '<<keep<<' '<<drop<<" cases "<<cases.size()<<" trials "<<trials<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begun).count()<<endl;
 }
 done:cout<<"DONE pairs "<<pairs<<" trials "<<trials<<" hits "<<hits<<" timedout "<<timed()<<endl;
}
