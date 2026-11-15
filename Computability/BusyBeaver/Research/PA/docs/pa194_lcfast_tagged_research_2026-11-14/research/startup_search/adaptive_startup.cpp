// Adaptive encountered-row repair search for the inherited Runtime193 core.
// Whole-frame recognizer adapted from the attributed AX11 pair_startup.cpp.
// Search candidates are not accepted runtime-preserving machines.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <string>
#include <tuple>
#include <unordered_set>
#include <vector>
#include <utility>
using namespace std;
struct A {int w,d,n;}; struct Edit {int id,q,b,group;A a;};
struct Seed{int pc;string path;int mask;};
constexpr int W=50001,O=25000,MAXQ=4096;
array<A,2> base[MAXQ],rows[MAXQ];bool ex[MAXQ]{};vector<int>states;
vector<Edit>es;vector<Seed>seeds;int rowgroup[2*MAXQ]; vector<vector<int>>bygroup;
struct Config {int start; vector<int> ids; bitset<128> seen;int score=0,status=0,steps=0,ones=0,lastq=0,lasthead=0;uint64_t hash=0,rank=0;};
long long runs=0,ticks=0,hits=0,rays=0,limits=0,halts=0,q84=0; int BOUND=50000,WIDTH=512,MAXDEPTH=12;double SECONDS=240;
mt19937_64 rng(5082193);auto time0=chrono::steady_clock::now();
string tag(const Config& c) {string s=to_string(c.start)+":";for(int i:c.ids)s+=to_string(i)+",";return s;}
uint64_t mix(uint64_t x){x+=0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}
int detect(Config &c,const unsigned char *t,int h,int mi,int ma,int st){
 if(mi!=h-1)return 0;
 int score=100;
 for(auto &s:seeds){
  int p=h,matched=0;
  for(char ch:s.path){if(t[p++]!=ch-'0')break;matched++;}
  score=max(score,100+matched*10);
  if(matched!=(int)s.path.size())continue;
  while(p<=ma&&!t[p])p++;
  if(p>ma)continue;
  if(p<h+48){score=max(score,200+min(p-h,48));continue;}
  int header=p; vector<int>vals;bool ok=true;
  while(p<ma){
   if(t[++p]||!t[++p]){ok=false;break;}
   int len=0;while(p<=ma&&t[p]){len++;p++;}vals.push_back(len-1);p--;
  }
  score=max(score,300+(int)vals.size()*100+(ok?50:0));
  if(ok&&vals.size()>=10){
   hits++;c.score=100000;c.status=1;
   cout<<"{\"start\":"<<c.start<<",\"edits\":[";for(size_t i=0;i<c.ids.size();i++){if(i)cout<<',';cout<<c.ids[i];}
   cout<<"],\"steps\":"<<st<<",\"pc\":"<<s.pc<<",\"head\":"<<h-O<<",\"gap\":"<<header-h-48<<",\"values\":[";
   for(size_t i=0;i<vals.size();i++){if(i)cout<<',';cout<<vals[i];}cout<<"],\"support\":[";bool first=true;for(int j=mi;j<=ma;j++)if(t[j]){if(!first)cout<<',';first=false;cout<<j-O;}cout<<"]}"<<endl;
   return 1;
  }
 }
 c.score=max(c.score,score);return 0;
}
void simulate(Config &c){
 static unsigned char t[W];memset(t,0,W);for(int q:states)rows[q]=base[q];for(int i:c.ids){auto e=es[i];rows[e.q][e.b]=e.a;}
 int q=c.start,h=O,mi=O,ma=O,ones=0;uint64_t hash=0; c.seen.reset();c.score=0;c.status=0;
 runs++;
 for(int st=0;;st++){
  c.steps=st;c.ones=ones;c.lastq=q;c.lasthead=h-O;c.hash=hash;
  if(q==254){halts++;c.status=2;break;}
  if(st>=BOUND||h<100||h>=W-100||ones>20000){limits++;c.status=3;break;}
  if(!ex[q]){c.status=5;break;}
  if(q==84){q84++;if(ones>=13){while(mi<=ma&&!t[mi])mi++;while(ma>=mi&&!t[ma])ma--;if(detect(c,t,h,mi,ma,st))break;}}
  int b=t[h],g=rowgroup[2*q+b];if(g>=0)c.seen[g]=true;
  A a=rows[q][b];
  if(!b&&a.n==q&&((a.d==1&&h>ma)||(a.d==-1&&h<mi)||!ones)){rays++;c.status=4;break;}
  if(a.w!=b){ones+=a.w-b;t[h]=a.w;hash^=mix(h);if(a.w){mi=min(mi,h);ma=max(ma,h);}}
  h+=a.d;q=a.n;ticks++;
 }
 c.rank=rng();
}
bool elite(const Config&a,const Config&b){if(a.score!=b.score)return a.score>b.score;return a.rank<b.rank;}
int main(int argc,char**argv){
 if(argc<4){cerr<<"table edits templates [depth width step_bound seconds start=-1 seed]"<<endl;return 2;}
 if(argc>4)MAXDEPTH=stoi(argv[4]);if(argc>5)WIDTH=stoi(argv[5]);if(argc>6)BOUND=stoi(argv[6]);if(argc>7)SECONDS=stod(argv[7]);int start=argc>8?stoi(argv[8]):-1;if(argc>9)rng.seed(stoull(argv[9]));
 ifstream f(argv[1]);int q,b,w,n;char dir;while(f>>q>>b>>w>>dir>>n){if(!ex[q])states.push_back(q);ex[q]=true;base[q][b]={w,dir=='R'?1:-1,n};}
 fill(rowgroup,rowgroup+2*MAXQ,-1);ifstream ef(argv[2]);Edit e;while(ef>>e.id>>e.q>>e.b>>e.a.w>>e.a.d>>e.a.n){int &g=rowgroup[2*e.q+e.b];if(g<0){g=bygroup.size();bygroup.push_back({});}e.group=g;bygroup[g].push_back(es.size());es.push_back(e);}
 ifstream sf(argv[3]);Seed s;while(sf>>s.pc>>s.path>>s.mask)seeds.push_back(s);
 unordered_set<string>done;vector<Config>beam;
 for(int q:states)if(start<0||q==start){Config c;c.start=q;simulate(c);done.insert(tag(c));beam.push_back(c);}
 cerr<<"BASE runs "<<runs<<" hits "<<hits<<" halts "<<halts<<" rays "<<rays<<" limits "<<limits<<endl;
 for(int depth=1;depth<=MAXDEPTH;depth++){
  vector<Config>children;long long before=runs;
  for(auto &parent:beam){
   bitset<128>used;for(int i:parent.ids)used[es[i].group]=true;
   for(size_t g=0;g<bygroup.size();g++)if(parent.seen[g]&&!used[g])for(int i:bygroup[g]){
    Config c;c.start=parent.start;c.ids=parent.ids;c.ids.push_back(i);sort(c.ids.begin(),c.ids.end());
    if(!done.insert(tag(c)).second)continue;simulate(c);children.push_back(move(c));
    if(runs%50000==0)cerr<<"progress depth "<<depth<<" runs "<<runs<<" ticks "<<ticks<<" hits "<<hits<<endl;
    if(chrono::duration<double>(chrono::steady_clock::now()-time0).count()>SECONDS)goto finished;
   }
  }
  if(children.empty())break;
  // Keep score elites plus behaviorally diverse configurations selected reproducibly.
  sort(children.begin(),children.end(),elite);beam.clear();unordered_set<string>picked;
  int top=min((int)children.size(),max(16,WIDTH/4));for(int i=0;i<top;i++){picked.insert(tag(children[i]));beam.push_back(move(children[i]));}
  map<tuple<int,int,int,int>,vector<int>>bins;
  for(size_t i=top;i<children.size();i++){auto &c=children[i];int os=c.ones==0?0:32-__builtin_clz(c.ones);bins[{c.score/100,c.status,c.lastq,os}].push_back(i);}
  vector<vector<int>>groups;for(auto &[k,v]:bins){shuffle(v.begin(),v.end(),rng);groups.push_back(move(v));}shuffle(groups.begin(),groups.end(),rng);
  for(size_t round=0;beam.size()<(size_t)WIDTH;round++){
   bool any=false;for(auto &v:groups)if(round<v.size()){any=true;int i=v[round];if(beam.size()<(size_t)WIDTH)beam.push_back(move(children[i]));}if(!any)break;
  }
  int best=0;for(auto&c:beam)best=max(best,c.score);
  cerr<<"DEPTH "<<depth<<" new_runs "<<runs-before<<" beam "<<beam.size()<<" best "<<best<<" total_runs "<<runs<<" ticks "<<ticks<<" hits "<<hits<<" halts "<<halts<<" rays "<<rays<<" limits "<<limits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-time0).count()<<endl;
  if(!beam.empty())for(int j=0;j<min(3,(int)beam.size());j++){auto&c=beam[j];cerr<<"TOP "<<tag(c)<<" score "<<c.score<<" status "<<c.status<<" steps "<<c.steps<<" ones "<<c.ones<<" q "<<c.lastq<<endl;}
 }
 finished:
 cerr<<"DONE runs "<<runs<<" ticks "<<ticks<<" hits "<<hits<<" halts "<<halts<<" rays "<<rays<<" limits "<<limits<<" q84 "<<q84<<" distinct_configs "<<done.size()<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-time0).count()<<endl;
 return 0;
}
