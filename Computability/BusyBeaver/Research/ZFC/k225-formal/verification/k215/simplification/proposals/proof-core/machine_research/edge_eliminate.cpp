#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Row {int w,d,t;};
struct Cfg {int s,h,b;};
static const int NS=1024;
array<array<Row,2>,NS> tab;
array<bool,NS> live{};
array<array<bool,2>,NS> defined{};
int radius=5,cap=48,width=11,W=2048,M=2047,start=0;
uint64_t key(Cfg c) {return (uint64_t(c.b)<<16)|(uint64_t(c.s)<<5)|uint64_t(c.h+radius+1);}
int readbit(Cfg c) {return (c.b>>(c.h+radius))&1;}
Cfg step(Cfg c,Row r) {int k=c.h+radius; c.b=(c.b&~(1<<k))|(r.w<<k);c.h+=r.d;c.s=r.t;return c;}
vector<uint64_t> oldpath(int p,int bits) {
 Cfg c{p,0,bits};vector<uint64_t> a;
 for(int t=0;t<cap;t++) {if(!live[c.s]||c.h < -radius||c.h>radius)break;c=step(c,tab[c.s][readbit(c)]);a.push_back(key(c));}
 sort(a.begin(),a.end());a.erase(unique(a.begin(),a.end()),a.end());return a;
}
bool reaches(int p,int bits,int removed,Row first,vector<uint64_t> const& targets) {
 Cfg c=step(Cfg{p,0,bits},first);
 for(int t=1;t<=cap;t++) {
  if(binary_search(targets.begin(),targets.end(),key(c)))return true;
  if(c.s==removed||!live[c.s]||c.h < -radius||c.h>radius)return false;
  int b=readbit(c);Row r=tab[c.s][b];
  // No patched incoming row may occur in a strict new-block interior.
  if(r.t==removed)return false;
  c=step(c,r);
 }
 return false;
}
int main(int argc,char** argv) {
 if(argc<2){cerr<<"usage: edge_eliminate TABLE [RADIUS [CAP]]\n";return 2;}
 if(argc>2)radius=stoi(argv[2]);if(argc>3)cap=stoi(argv[3]);
 assert(radius>=1&&radius<=7);width=2*radius+1;W=1<<width;M=W-1;
 ifstream in(argv[1]);string line;vector<int> states;int rows=0;
 while(getline(in,line)){if(line.rfind("#! start ",0)==0){start=stoi(line.substr(9));continue;}if(line.empty()||line[0]=='#')continue;int p,b,w,q;char d;istringstream ss(line);if(!(ss>>p>>b>>w>>d>>q))continue;assert(0<=p&&p<NS&&0<=q&&q<NS);assert(b==0||b==1);assert(w==0||w==1);assert(d=='R'||d=='L');assert(!defined[p][b]);defined[p][b]=true;tab[p][b]={w,d=='R'?1:-1,q};live[p]=true;rows++;}
 for(int p=0;p<NS;p++)if(live[p]){assert(defined[p][0]&&defined[p][1]);states.push_back(p);}assert(rows==2*states.size());assert(live[start]);
 vector<unsigned char> seen(NS*W,0);vector<int> queue;queue.reserve(states.size()*W);
 auto add=[&](int s,int b){if(live[s]&&!seen[s*W+b]){seen[s*W+b]=1;queue.push_back(s*W+b);}};
 for(int b=0;b<W;b++)add(start,b);
 for(size_t i=0;i<queue.size();i++){int s=queue[i]/W,bits=queue[i]%W,b=(bits>>radius)&1;Row r=tab[s][b];int bits2=(bits&~(1<<radius))|(r.w<<radius);
  if(r.d==1){int shifted=bits2>>1;add(r.t,shifted);add(r.t,shifted|(1<<(width-1)));}
  else{int shifted=(bits2<<1)&M;add(r.t,shifted);add(r.t,shifted|1);}}
 vector<array<vector<int>,2>> contexts(NS);
 for(int s:states)for(int b=0;b<W;b++)if(seen[s*W+b])contexts[s][(b>>radius)&1].push_back(b);
 long long attempts=0,provedRows=0;int testedStates=0,passedStates=0,edgesChecked=0;vector<string> hits,partials;
 cerr<<"states "<<states.size()<<" contexts "<<queue.size()<<" radius "<<radius<<" cap "<<cap<<"\n";
 for(int q:states){if(q==start)continue;testedStates++;
  vector<pair<int,int>> inc;for(int p:states)if(p!=q)for(int b=0;b<2;b++)if(tab[p][b].t==q)inc.push_back({p,b});
  // Hardest-looking edge first; changes only enumeration order.
  sort(inc.begin(),inc.end(),[&](auto x,auto y){auto nx=contexts[x.first][x.second].size(),ny=contexts[y.first][y.second].size();return nx!=ny?nx>ny:x<y;});
  vector<string> patches;bool all=true;
  for(auto [p,b]:inc){edgesChecked++;vector<Row> candidates;
   vector<int> cs=contexts[p][b];
   if(cs.empty()){all=false;break;} // Do not exploit absent contexts in this experiment.
   vector<vector<uint64_t>> old;old.reserve(cs.size());for(int x:cs)old.push_back(oldpath(p,x));
   for(int w=0;w<2;w++)for(int d:{-1,1})for(int t=0;t<NS;t++)if((live[t]&&t!=q)||(!live[t]&&t==254)) {
    Row r{w,d,t};attempts++;bool ok=true;
    for(size_t j=0;j<cs.size();j++)if(!reaches(p,cs[j],q,r,old[j])){ok=false;break;}
    if(ok)candidates.push_back(r);
   }
   if(candidates.empty()){all=false;break;}
   provedRows++;Row r=candidates.front();ostringstream x;x<<"["<<p<<","<<b<<","<<r.w<<",\""<<(r.d==1?'R':'L')<<"\","<<r.t<<"]";patches.push_back(x.str());
   ostringstream pr;pr<<"{\"remove\":"<<q<<",\"source\":["<<p<<","<<b<<"],\"contexts\":"<<cs.size()<<",\"valid_replacements\":"<<candidates.size()<<",\"first_patch\":"<<x.str()<<"}";partials.push_back(pr.str());
  }
  if(all){passedStates++;ostringstream h;h<<"{\"remove\":"<<q<<",\"patch\":[";for(size_t i=0;i<patches.size();i++){if(i)h<<",";h<<patches[i];}h<<"]}";hits.push_back(h.str());cerr<<"HIT remove "<<q<<"\n";}
 }
 cout<<"{\"radius\":"<<radius<<",\"cap\":"<<cap<<",\"states\":"<<states.size()<<",\"start\":"<<start<<",\"contexts\":"<<queue.size()<<",\"tested_states\":"<<testedStates<<",\"edges_checked\":"<<edgesChecked<<",\"replacement_rows_tested\":"<<attempts<<",\"edges_with_replacements\":"<<provedRows<<",\"full_eliminations\":"<<passedStates<<",\"hits\":[";
 for(size_t i=0;i<hits.size();i++){if(i)cout<<",";cout<<hits[i];}cout<<"],\"partial_replacements\":[";for(size_t i=0;i<partials.size();i++){if(i)cout<<",";cout<<partials[i];}cout<<"]}\n";
}
