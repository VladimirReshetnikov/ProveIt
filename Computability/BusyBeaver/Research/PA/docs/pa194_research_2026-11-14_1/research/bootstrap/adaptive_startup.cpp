// Adaptive bounded bootstrap repair. New implementation for this report.
// Input and complete source-frame convention from the attributed PA194 packets.
#include <bits/stdc++.h>
using namespace std;
struct Act { int w,d,n; };
struct Edit { int id,q,b; Act a; };
struct Seed { int pc; string path; int any; };
struct Conf { int q=74,h=0,t=0; set<int> one; uint64_t hash=0; };
array<Act,2> rows[3000]; bool exists_[3000];
vector<Edit> choices[6000]; vector<Seed> seeds;
int bound=200000,maxed=3;
long long branches=0,leaves=0,ticks=0,halts=0,rays=0,cycles=0,limits=0,hits=0;
auto started=chrono::steady_clock::now();
uint64_t mix(uint64_t x) { x+=0x9e3779b97f4a7c15ULL; x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL; x=(x^(x>>27))*0x94d049bb133111ebULL; return x^(x>>31); }
void step(Conf& c) {
  auto a=rows[c.q][c.one.count(c.h)]; bool old=c.one.count(c.h);
  if(old!=bool(a.w)) { c.hash^=mix(uint64_t(int64_t(c.h))); if(a.w)c.one.insert(c.h);else c.one.erase(c.h); }
  c.h+=a.d;c.q=a.n;c.t++;ticks++;
}
bool ray(int q,int d,const bitset<6000>& fixed,int used) {
  bitset<3000> seen;
  for(;;){if(!exists_[q]||rows[q][0].d!=d)return false;
    if(used<maxed&&!fixed[2*q]&&!choices[2*q].empty())return false;
    if(seen[q])return true;seen[q]=true;q=rows[q][0].n;}
}
bool frame(const Conf& c,const vector<int>& edits) {
 if(c.q!=84||c.one.size()<13)return false;
 vector<int> x(c.one.begin(),c.one.end());
 for(auto&s:seeds){vector<int>pre{c.h-1};for(size_t k=0;k<s.path.size();k++)if(s.path[k]=='1')pre.push_back(c.h+k);
  size_t m=pre.size();bool ok=x.size()>m&&equal(pre.begin(),pre.end(),x.begin())&&x[m]>=c.h+48;
  if(!ok)continue;vector<int>values;size_t k=m+1;int pos=x[m];
  while(ok&&k<x.size()){if(x[k]!=pos+2){ok=false;break;}int len=1;pos=x[k++];while(k<x.size()&&x[k]==pos+1){len++;pos=x[k++];}values.push_back(len-1);}
  if(values.size()<10)ok=false;
  if(ok){hits++;cout<<"{\"edits\":[";for(size_t k=0;k<edits.size();k++){if(k)cout<<',';cout<<edits[k];}cout<<"],\"steps\":"<<c.t<<",\"pc\":"<<s.pc<<",\"head\":"<<c.h<<",\"values\":[";for(size_t k=0;k<values.size();k++){if(k)cout<<',';cout<<values[k];}cout<<"],\"ones\":[";for(size_t k=0;k<x.size();k++){if(k)cout<<',';cout<<x[k];}cout<<"]}"<<endl;return true;}
 }return false;
}
struct Seen {int q,h,t;size_t size;};
void explore(Conf c,bitset<6000> fixed,vector<int> edits) {
 branches++;Conf initial=c;unordered_map<uint64_t,Seen> seen;
 for(;;){
  if(c.q==254||!exists_[c.q]){halts++;break;}
  if(frame(c,edits))break;
  if(c.t==bound||abs(c.h)>20000||c.one.size()>20000){limits++;break;}
  bool bit=c.one.count(c.h);int key=2*c.q+bit;
  if(!fixed[key]&&!choices[key].empty()&&int(edits.size())<maxed){
    fixed[key]=true;Act old=rows[c.q][bit];
    for(auto&e:choices[key]){rows[c.q][bit]=e.a;auto next=edits;next.push_back(e.id);explore(c,fixed,next);}
    rows[c.q][bit]=old;
  }
  uint64_t hash=c.hash^mix(c.q+3000ULL)^mix(uint64_t(int64_t(c.h))+6000ULL);
  auto it=seen.find(hash);
  if(it!=seen.end()&&it->second.q==c.q&&it->second.h==c.h&&it->second.size==c.one.size()) {
    // A hash match only triggers a fresh exact replay; never rejects by hash alone.
    Conf old=initial;while(old.t<it->second.t)step(old);
    if(old.q==c.q&&old.h==c.h&&old.one==c.one){cycles++;break;}
  } else seen[hash]={c.q,c.h,c.t,c.one.size()};
  if(!bit){bool empty=c.one.empty();
    if((empty||*c.one.rbegin()<c.h)&&ray(c.q,1,fixed,edits.size())){rays++;break;}
    if((empty||*c.one.begin()>c.h)&&ray(c.q,-1,fixed,edits.size())){rays++;break;}
  }
  step(c);
 }
 leaves++;
 if(leaves%10000==0)cerr<<"leaves "<<leaves<<" branches "<<branches<<" ticks "<<ticks<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}
int main(int argc,char**argv) {
 if(argc<4){cerr<<"table edits seeds [max_edits] [bound]\n";return 2;}
 int q,b,w,n;char d;ifstream f(argv[1]);while(f>>q>>b>>w>>d>>n){exists_[q]=true;rows[q][b]={w,d=='R'?1:-1,n};}
 Edit e;ifstream ef(argv[2]);while(ef>>e.id>>e.q>>e.b>>e.a.w>>e.a.d>>e.a.n)choices[e.q*2+e.b].push_back(e);
 Seed s;ifstream sf(argv[3]);while(sf>>s.pc>>s.path>>s.any)seeds.push_back(s);
 if(argc>4)maxed=stoi(argv[4]);if(argc>5)bound=stoi(argv[5]);
 explore(Conf(),bitset<6000>(),{});
 cerr<<"DONE edits "<<maxed<<" bound "<<bound<<" branches "<<branches<<" leaves "<<leaves<<" ticks "<<ticks<<" halts "<<halts<<" rays "<<rays<<" cycles "<<cycles<<" limits "<<limits<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}
