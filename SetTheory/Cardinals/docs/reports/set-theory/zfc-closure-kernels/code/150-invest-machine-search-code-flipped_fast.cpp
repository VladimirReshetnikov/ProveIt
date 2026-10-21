#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
struct A {int w,d,z;bool operator==(const A&x)const{return w==x.w&&d==x.d&&z==x.z;}};
struct Path {vector<uint64_t> goals;bool halts=false;};
struct Group {int q,b;vector<uint32_t> words;};
array<array<A,2>,400> oldtab,newtab;array<vector<uint32_t>,400> inv;
vector<int> states;vector<A> actions;vector<pair<int,int>> pairs;
array<Group,4> groups;array<int,4> order;unordered_map<uint64_t,Path> cache;
int radius,fuel,keep,drop,tag,start=0;uint64_t partial,covered,survivors,totalpartial=0,totalcovered=0;bool stopped=false;string prefix;
auto began=chrono::steady_clock::now(),deadline=began;
int phi(int q){return q==drop?keep:q;}
uint64_t encode(int q,int h,uint32_t m){return (uint64_t(m)<<15)|(uint64_t(h+radius+1)<<9)|q;}
bool due(){return chrono::steady_clock::now()>=deadline;}
Path& oldpath(int q,uint32_t word){
 uint64_t key=(uint64_t(word)<<9)|q;auto found=cache.find(key);if(found!=cache.end())return found->second;
 Path p;int h=0;uint32_t m=word;vector<uint64_t> visited;
 for(int tick=0;tick<fuel;tick++){
  if(q==254||h < -radius||h>radius)break;
  uint64_t conf=encode(q,h,m);if(find(visited.begin(),visited.end(),conf)!=visited.end())break;visited.push_back(conf);
  int b=(m>>(h+radius))&1;A a=oldtab[q][b];m=(m&~(1u<<(h+radius)))|(a.w<<(h+radius));h+=a.d;q=a.z;
  if(q!=drop)p.goals.push_back(encode(q,h,m));else if(h+tag>=-radius&&h+tag<=radius)p.goals.push_back(encode(keep,h,m^(1u<<(h+tag+radius))));if(q==254)p.halts=true;
 }
 return cache.emplace(key,move(p)).first->second;
}
// Return -1 for rejection, 0 or 1 for a required unassigned row, 2 for pass.
int check(){
 auto sequence=order;
 for(int gi:sequence){
  Group&g=groups[gi];A oa=oldtab[g.q][g.b];oa.w^=(oa.z==drop);oa.z=phi(oa.z);if(g.q!=drop&&newtab[keep][g.b]==oa)continue;
  for(size_t i=0;i<g.words.size();i++){
   if((i&255)==0&&due()){stopped=true;return -1;}
   uint32_t word=g.words[i];Path&p=oldpath(g.q,word);int q=keep,h=0,need=-1;uint32_t m=word^((g.q==drop)?(1u<<(tag+radius)):0);bool joined=false;vector<uint64_t>visited;visited.reserve(40);
   for(int tick=0;tick<fuel;tick++){
    if(q==254||h < -radius||h>radius)break;
    uint64_t conf=encode(q,h,m);if(find(visited.begin(),visited.end(),conf)!=visited.end())break;visited.push_back(conf);
    int b=(m>>(h+radius))&1;A a=newtab[q][b];if(a.z==-1){need=b;break;}
    m=(m&~(1u<<(h+radius)))|(a.w<<(h+radius));h+=a.d;q=a.z;
    if(q==254){joined=p.halts;break;}
    uint64_t target=encode(q,h,m);if(find(p.goals.begin(),p.goals.end(),target)!=p.goals.end()){joined=true;break;}
   }
   if(!joined){auto it=find(order.begin(),order.end(),gi);rotate(order.begin(),it,it+1);if(i)swap(g.words[0],g.words[i]);return need;}
  }
 }
 return 2;
}
void writehit(){
 string path=prefix+"-hit"+to_string(survivors)+".native.tm";ofstream out(path);out<<"#! start "<<phi(start)<<"\n";
 for(int q:states)if(q!=drop)for(int b=0;b<2;b++){A a=newtab[q][b];out<<q<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.z<<'\n';}
 cout<<"HIT "<<keep<<' '<<drop<<' '<<path<<endl;
}
void walk(int depth){
 if(stopped||due()){stopped=true;return;}partial++;int outcome=check();if(stopped)return;
 if(outcome==-1){covered+=depth==0?actions.size()*actions.size():depth==1?actions.size():1;return;}
 if(outcome==2){
  if(newtab[keep][0].z==-1)outcome=0;else if(newtab[keep][1].z==-1)outcome=1;
  else{writehit();survivors++;stopped=true;return;}
 }
 if(newtab[keep][outcome].z!=-1){cerr<<"assigned need";exit(3);}
 for(A a:actions){newtab[keep][outcome]=a;walk(depth+1);if(stopped)break;}
 newtab[keep][outcome]={0,0,-1};
}
int main(int argc,char**argv){
 if(argc<4){cerr<<"Usage: twoaction_fast INPUT OUTPUT_PREFIX SECONDS\n";return 2;}
 ifstream in(argv[1]);prefix=argv[2];int n;in>>radius>>fuel>>start>>n;
 for(int i=0;i<n;i++){int q,c;in>>q;states.push_back(q);for(int b=0;b<2;b++)in>>oldtab[q][b].w>>oldtab[q][b].d>>oldtab[q][b].z;in>>c;inv[q].resize(c);for(auto&w:inv[q])in>>w;}
 in>>n;for(int i=0;i<n;i++){int q,r;in>>q>>r;pairs.emplace_back(q,r);}if(!in){cerr<<"malformed input";return 2;}
 began=chrono::steady_clock::now();deadline=began+chrono::seconds(stoi(argv[3]));ofstream report(prefix+"-records.tsv");report<<"keep\tdrop\tpartial_checks\tcovered_rejections\tsurvivors\tcomplete\n";int done=0;
 for(auto [q,r]:pairs){
  keep=q;drop=r;tag=0;for(int p:states)for(int b=0;b<2;b++)if(oldtab[p][b].z==drop){int t=-oldtab[p][b].d;if(tag&&tag!=t){cerr<<"mixed entry directions";return 3;}tag=t;}if(!tag||drop==start){cerr<<"invalid marker pair";return 3;}cache.clear();partial=covered=survivors=0;stopped=false;actions.clear();newtab=oldtab;
  for(int p:states)for(int b=0;b<2;b++){newtab[p][b].w^=(newtab[p][b].z==drop);newtab[p][b].z=phi(newtab[p][b].z);}
  newtab[keep][0]=newtab[keep][1]={0,0,-1};
  for(int w:{0,1})for(int d:{-1,1}){for(int z:states)if(z!=drop)actions.push_back({w,d,z});actions.push_back({w,d,254});}
  int gi=0;for(int p:{keep,drop})for(int b:{0,1}){groups[gi].q=p;groups[gi].b=b;groups[gi].words.clear();for(auto m:inv[p])if(int(m>>radius&1)==b)groups[gi].words.push_back(m);auto&v=groups[gi].words;if(v.size()>2)swap(v[1],v.back());order[gi]=gi;gi++;}
  walk(0);bool complete=!stopped;report<<keep<<'\t'<<drop<<'\t'<<partial<<'\t'<<covered<<'\t'<<survivors<<'\t'<<complete<<'\n';report.flush();totalpartial+=partial;totalcovered+=covered;done++;
  if(complete&&covered+survivors!=actions.size()*actions.size()){cerr<<"census mismatch";return 3;}
  if(done%100==0||stopped)cout<<"PROGRESS "<<done<<'/'<<pairs.size()<<" partial "<<totalpartial<<" covered "<<totalcovered<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;
  if(stopped)break;
 }
 cout<<"DONE "<<done<<'/'<<pairs.size()<<" partial "<<totalpartial<<" covered "<<totalcovered<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;
}
