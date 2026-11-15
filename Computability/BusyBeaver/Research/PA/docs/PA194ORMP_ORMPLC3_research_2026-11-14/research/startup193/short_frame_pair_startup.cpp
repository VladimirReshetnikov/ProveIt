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
struct Trie{int next[2]={-1,-1};int pc=-1;};
int main(int argc,char**argv){
 if(argc!=6){cerr<<"table edits templates fuel hits_file\n";return 2;}
 int fuel=stoi(argv[4]);array<array<A,2>,3000>base{},row{};
 array<bool,3000>exists{};vector<int>qs;int q,b,w,n;char dir;
 ifstream ti(argv[1]);while(ti>>q>>b>>w>>dir>>n){if(!exists[q])qs.push_back(q);exists[q]=true;base[q][b]={w,dir=='R'?1:-1,n};}
 vector<E>edits;E e;ifstream ei(argv[2]);while(ei>>e.id>>e.q>>e.b>>e.w>>e.d>>e.n)edits.push_back(e);
 vector<Seed>seeds;Seed s;ifstream si(argv[3]);while(si>>s.pc>>s.path>>s.mask)seeds.push_back(s);
 if(qs.size()!=193||seeds.empty()||edits.empty())return 3;
 vector<Trie> trie(1);
 for(const Seed&s:seeds){int a=0;for(char c:s.path){int b=c-'0';if(trie[a].next[b]<0){int nn=trie.size();trie[a].next[b]=nn;trie.emplace_back();}a=trie[a].next[b];}trie[a].pc=s.pc;}
 ofstream hits(argv[5]);long long pairs=0,sims=0,ticks=0,halts=0,rays=0,bounded=0,found=0;
 const int RAD=20000,OFF=RAD+1;vector<unsigned int>tape(2*RAD+3);unsigned int epoch=0;
 auto begin=chrono::steady_clock::now();
 for(size_t ia=0;ia<edits.size();++ia){for(size_t ib=ia+1;ib<edits.size();++ib){
  E a=edits[ia],c=edits[ib];if(a.q==c.q&&a.b==c.b)continue;
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
    if(q==84&&ones>=12&&left==h-1&&h+38<RAD){
     int node=0,len=0;
     while(trie[node].pc<0 && len<38){int v=tape[h+len+OFF]==epoch;node=trie[node].next[v];++len;if(node<0)break;}
     if(node>=0 && trie[node].pc>=0){
      int sep=h+len;while(sep<=right && tape[sep+OFF]!=epoch)++sep;
      if(sep>=h+len && sep<=right){
       vector<int>vals;int p=sep;bool ok=true;
       while(p<right){if(tape[p+1+OFF]==epoch || tape[p+2+OFF]!=epoch){ok=false;break;}
        p+=2;int count=0;while(p<right && tape[p+1+OFF]==epoch){++count;++p;}vals.push_back(count);
       }
       if(ok && vals.size()>=10){
        vector<int>pos;for(int j=left;j<=right;++j)if(tape[j+OFF]==epoch)pos.push_back(j);
        ++found;hits<<"{\"edits\":["<<a.id<<","<<c.id<<"],\"start\":"<<start<<",\"steps\":"<<st<<",\"site\":"<<trie[node].pc<<",\"head\":"<<h<<",\"span\":"<<sep-h<<",\"values\":[";
        for(size_t j=0;j<vals.size();++j){if(j)hits<<',';hits<<vals[j];}hits<<"],\"ones\":[";
        for(size_t j=0;j<pos.size();++j){if(j)hits<<',';hits<<pos[j];}hits<<"]}\n";hits.flush();break;
       }
      }
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
