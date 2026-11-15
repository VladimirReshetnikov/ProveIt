// Exhaustive bounded screen over the supplied finite two-edit pool.
// A frame hit would require separate runtime and semantic validation.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct A{int w,d,n;};
struct E{int id,q,b,w,d,n;};
struct Seed{int pc;string path;int mask;};
int main(int argc,char**argv){
 if(argc!=6){cerr<<"table edits templates fuel hits_file\n";return 2;}
 int fuel=stoi(argv[4]);array<array<A,2>,3000>base{},row{};
 array<bool,3000>exists{};vector<int>qs;int q,b,w,n;char dir;
 ifstream ti(argv[1]);while(ti>>q>>b>>w>>dir>>n){if(!exists[q])qs.push_back(q);exists[q]=true;base[q][b]={w,dir=='R'?1:-1,n};}
 vector<E>edits;E e;ifstream ei(argv[2]);while(ei>>e.id>>e.q>>e.b>>e.w>>e.d>>e.n)edits.push_back(e);
 vector<Seed>seeds;Seed s;ifstream si(argv[3]);while(si>>s.pc>>s.path>>s.mask)seeds.push_back(s);
 if(qs.size()!=193||seeds.size()!=20||edits.empty())return 3;
 ofstream hits(argv[5]);long long pairs=0,sims=0,ticks=0,halts=0,rays=0,bounded=0,found=0;
 const int RAD=20000,OFF=RAD+1;vector<unsigned int>tape(2*RAD+3);unsigned int epoch=0;
 auto begin=chrono::steady_clock::now();
 for(size_t ia=0;ia<edits.size();++ia){for(size_t ib=ia+1;ib<edits.size();++ib){
  E a=edits[ia],c=edits[ib];if(a.q==c.q&&a.b==c.b)continue; if(ib<346)continue;
  ++pairs;row=base;row[a.q][a.b]={a.w,a.d,a.n};row[c.q][c.b]={c.w,c.d,c.n};
  array<int,3000>raydir{};
  for(int first:qs){int r=first,d=0;set<int>seen;
   while(r>=0&&r<3000&&exists[r]&&!seen.count(r)){seen.insert(r);A x=row[r][0];if(d&&x.d!=d){d=0;break;}d=x.d;r=x.n;}
   if(d&&seen.count(r))raydir[first]=d;
  }
  for(int start:qs){++sims;++epoch;if(!epoch){fill(tape.begin(),tape.end(),0);++epoch;}
   int q=start,h=0,ones=0,left=1,right=-1;
   for(int st=0;;++st){
    if(q<0||q>=3000||!exists[q]){++halts;break;}
    if(q==84&&ones>=13){vector<int>pos;for(int j=left;j<=right;++j)if(tape[j+OFF]==epoch)pos.push_back(j);
     for(const Seed&s:seeds){vector<int>pref{h-1};for(size_t j=0;j<s.path.size();++j)if(s.path[j]=='1')pref.push_back(h+j);
      size_t m=pref.size();if(pos.size()<=m||!equal(pref.begin(),pref.end(),pos.begin())||pos[m]<h+48)continue;
      vector<int>vals;size_t j=m+1;int p=pos[m];bool ok=true;
      while(j<pos.size()){if(pos[j]!=p+2){ok=false;break;}int len=1;p=pos[j++];while(j<pos.size()&&pos[j]==p+1){++len;p=pos[j++];}vals.push_back(len-1);}
      if(!ok||vals.size()<10)continue;
      ++found;hits<<"{\"edits\":["<<a.id<<","<<c.id<<"],\"start\":"<<start<<",\"steps\":"<<st<<",\"site\":"<<s.pc<<",\"head\":"<<h<<",\"values\":[";
      for(size_t j=0;j<vals.size();++j){if(j)hits<<',';hits<<vals[j];}hits<<"],\"ones\":[";
      for(size_t j=0;j<pos.size();++j){if(j)hits<<',';hits<<pos[j];}hits<<"]}\n";hits.flush();break;
     }
    }
    if(st>=fuel||abs(h)>=RAD){++bounded;break;}
    bool bit=tape[h+OFF]==epoch;int rd=raydir[q];
    if(!bit&&rd&&(!ones||(rd==1&&h>right)||(rd==-1&&h<left))){++rays;break;}
    A x=row[q][bit];
    if(x.w&&!bit){tape[h+OFF]=epoch;++ones;if(ones==1)left=right=h;else{left=min(left,h);right=max(right,h);}}
    else if(!x.w&&bit){tape[h+OFF]=0;--ones;if(!ones){left=1;right=-1;}else{if(h==left)while(tape[++left+OFF]!=epoch){};if(h==right)while(tape[--right+OFF]!=epoch){}}}
    h+=x.d;q=x.n;++ticks;
   }
  }
 }if(ia%25==0)cerr<<"first "<<ia<<" pairs "<<pairs<<" transitions "<<ticks<<" hits "<<found<<'\n';}
 cout<<"{\"candidate_edits\":"<<edits.size()<<",\"pairs\":"<<pairs<<",\"starts_per_pair\":"<<qs.size()<<",\"simulations\":"<<sims<<",\"transitions\":"<<ticks<<",\"halts\":"<<halts<<",\"outward_rays\":"<<rays<<",\"bounded\":"<<bounded<<",\"frame_hits\":"<<found<<",\"fuel\":"<<fuel<<",\"head_bound\":"<<RAD<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<"}\n";
}
