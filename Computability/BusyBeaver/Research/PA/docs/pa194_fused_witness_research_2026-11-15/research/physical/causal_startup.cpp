// Causal finite bootstrap search. Each new edit must affect an observed row.
// A hit is only a physical frame and still needs semantic/runtime validation.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>
#include <unordered_set>
#include <functional>
using namespace std;
struct A{int w,d,n;};
struct E{int id,q,b,w,d,n;};
struct Seed{int pc;string path;int mask;};
int main(int argc,char**argv){
 if(argc!=9 && argc!=10){cerr<<"table edits templates fuel maxdepth start maxnodes hits_file\n";return 2;}
 int fuel=stoi(argv[4]),maxdepth=stoi(argv[5]),start=stoi(argv[6]);long long maxnodes=stoll(argv[7]);
 long long maxTicks=argc==10?stoll(argv[9]):9000000000000000000LL;
 array<array<A,2>,3000>base{},row{};array<bool,3000>exists{};vector<int>qs;int q,b,w,n;char dir;
 ifstream ti(argv[1]);while(ti>>q>>b>>w>>dir>>n){if(!exists[q])qs.push_back(q);exists[q]=true;base[q][b]={w,dir=='R'?1:-1,n};}
 vector<E>edits;E e;ifstream ei(argv[2]);while(ei>>e.id>>e.q>>e.b>>e.w>>e.d>>e.n)edits.push_back(e);
 vector<Seed>seeds;Seed s;ifstream si(argv[3]);while(si>>s.pc>>s.path>>s.mask)seeds.push_back(s);
 vector<vector<int>>byrow(6000);for(int i=0;i<(int)edits.size();++i)byrow[2*edits[i].q+edits[i].b].push_back(i);
 ofstream hits(argv[8]);long long sims=0,ticks=0,halts=0,rays=0,bounded=0,found=0;
 const int RAD=20000,OFF=RAD+1;vector<unsigned int>tape(2*RAD+3);unsigned int epoch=0;
 auto begin=chrono::steady_clock::now();unordered_set<unsigned long long>seen;seen.reserve(1000000);
 vector<int>chosen;array<bool,6000>edited{};row=base;
 function<void()> dfs=[&](){
  if(sims>=maxnodes||ticks>=maxTicks||found)return;
  vector<int>ids=chosen;sort(ids.begin(),ids.end());unsigned long long key=1;
  for(int i:ids)key=key*512+(i+1);
  if(!seen.insert(key).second)return;
  ++sims;++epoch;if(!epoch){fill(tape.begin(),tape.end(),0);++epoch;}
  array<bool,6000>visited{};vector<int>tracekeys;array<int,3000>raydir{};
  int q=start,h=0,ones=0,left=1,right=-1;
  for(int st=0;;++st){
   if(q<0||q>=3000||!exists[q]){++halts;break;}
   if(q==84&&ones>=13){vector<int>pos;for(int j=left;j<=right;++j)if(tape[j+OFF]==epoch)pos.push_back(j);
    for(const Seed&s:seeds){vector<int>pref{h-1};for(size_t j=0;j<s.path.size();++j)if(s.path[j]=='1')pref.push_back(h+j);
     size_t m=pref.size();if(pos.size()<=m||!equal(pref.begin(),pref.end(),pos.begin())||pos[m]<h+48)continue;
     vector<int>vals;size_t j=m+1;int p=pos[m];bool ok=true;
     while(j<pos.size()){if(pos[j]!=p+2){ok=false;break;}int len=1;p=pos[j++];while(j<pos.size()&&pos[j]==p+1){++len;p=pos[j++];}vals.push_back(len-1);}
     if(!ok||vals.size()<10)continue;
     ++found;hits<<"{\"edits\":[";for(size_t k=0;k<ids.size();++k){if(k)hits<<',';hits<<ids[k];}
     hits<<"],\"start\":"<<start<<",\"steps\":"<<st<<",\"site\":"<<s.pc<<",\"head\":"<<h<<",\"values\":[";
     for(size_t k=0;k<vals.size();++k){if(k)hits<<',';hits<<vals[k];}hits<<"],\"ones\":[";
     for(size_t k=0;k<pos.size();++k){if(k)hits<<',';hits<<pos[k];}hits<<"]}\n";hits.flush();break;
    }
    if(found)break;
   }
   if(st>=fuel||abs(h)>=RAD){++bounded;break;}
   bool bit=tape[h+OFF]==epoch;int key=2*q+bit;if(!visited[key]){visited[key]=true;tracekeys.push_back(key);}
   if(!bit&&(!ones||h>right||h<left)){
    if(raydir[q]==0){int r=q,d=0;set<int>rr;
     while(r>=0&&r<3000&&exists[r]&&!rr.count(r)){rr.insert(r);A a=row[r][0];if(d&&a.d!=d){d=0;break;}d=a.d;r=a.n;}
     raydir[q]=(d&&rr.count(r))?d:2;
    }
    int rd=raydir[q];
    if(rd!=2&&(!ones||(rd==1&&h>right)||(rd==-1&&h<left))){
     // Include every row of the certified outward path: editing one can break the ray.
     int r=q;set<int>rr;while(!rr.count(r)){rr.insert(r);int k=2*r;if(!visited[k]){visited[k]=true;tracekeys.push_back(k);}r=row[r][0].n;}
     ++rays;break;
    }
   }
   A a=row[q][bit];
   if(a.w&&!bit){tape[h+OFF]=epoch;++ones;if(ones==1)left=right=h;else{left=min(left,h);right=max(right,h);}}
   else if(!a.w&&bit){tape[h+OFF]=0;--ones;if(!ones){left=1;right=-1;}else{if(h==left)while(tape[++left+OFF]!=epoch){};if(h==right)while(tape[--right+OFF]!=epoch){}}}
   h+=a.d;q=a.n;++ticks;
  }
  if(sims%10000==0)cerr<<"simulations "<<sims<<" transitions "<<ticks<<" bounded "<<bounded<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<'\n';
  if((int)chosen.size()==maxdepth||found)return;
  for(int k:tracekeys)if(!edited[k])for(int id:byrow[k]){
   E a=edits[id];A old=row[a.q][a.b];row[a.q][a.b]={a.w,a.d,a.n};chosen.push_back(id);edited[k]=true;
   dfs();edited[k]=false;chosen.pop_back();row[a.q][a.b]=old;if(sims>=maxnodes||ticks>=maxTicks||found)return;
  }
 };
 dfs();
 cout<<"{\"candidate_edits\":"<<edits.size()<<",\"depth\":"<<maxdepth<<",\"start\":"<<start<<",\"simulations\":"<<sims<<",\"transitions\":"<<ticks<<",\"halts\":"<<halts<<",\"outward_rays\":"<<rays<<",\"bounded\":"<<bounded<<",\"frame_hits\":"<<found<<",\"fuel\":"<<fuel<<",\"head_bound\":"<<RAD<<",\"node_cap\":"<<maxnodes<<",\"cap_reached\":"<<(sims>=maxnodes?"true":"false")<<",\"transition_cap\":"<<maxTicks<<",\"transition_cap_reached\":"<<(ticks>=maxTicks?"true":"false")<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<"}\n";
}
