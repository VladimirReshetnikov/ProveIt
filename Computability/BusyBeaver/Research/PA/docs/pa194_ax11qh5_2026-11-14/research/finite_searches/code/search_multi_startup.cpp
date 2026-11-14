#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;};
struct E {int id,q,b;A a;};
struct C {int q,h,t;set<int> ones;unsigned long long th=0;};
unsigned long long mix(unsigned long long x){x+=0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}
struct Seed {int pc;string path;int arb;};
array<array<A,2>,5000> base,row;array<bool,5000> ex{};array<vector<E>,10000> opts;array<bool,10000> decided{};vector<int> qs;vector<E> edits;vector<Seed> seeds;
long long nodes=0,steps=0,leaves=0,rays=0,halts=0,limits=0,successes=0,cycles=0;int budget=3,bound=250000,startq=74;long long cap=20000000;
bool ray(int q,int h,set<int> const&ones){
 int d=0;set<int> seen;
 while(ex[q]&&!seen.count(q)) {
  if(!decided[q*2]&&!opts[q*2].empty())return false;
  seen.insert(q);A a=row[q][0];if(d&&a.d!=d)return false;d=a.d;q=a.n;
 }
 if(!ex[q])return false;
 return d==1?(ones.empty()||*ones.rbegin()<h):(ones.empty()||*ones.begin()>h);
}
bool frame(C const&c){
 if(c.q!=84||c.ones.size()<13)return false;
 vector<int>x(c.ones.begin(),c.ones.end());
 for(auto s:seeds){vector<int> prefix{c.h-1};for(int j=0;j<(int)s.path.size();j++)if(s.path[j]=='1')prefix.push_back(c.h+j);size_t m=prefix.size();
 if(x.size()<=m||!equal(prefix.begin(),prefix.end(),x.begin())||x[m]<c.h+48)continue;
 vector<int>v;size_t i=m+1;int pos=x[m];bool ok=true;
 while(i<x.size()){if(x[i]!=pos+2){ok=false;break;}int len=1;pos=x[i++];while(i<x.size()&&x[i]==pos+1){len++;pos=x[i++];}v.push_back(len-1);}
 if(!ok||v.size()<10)continue;
 successes++;cout<<"{\"start\":"<<startq<<",\"step\":"<<c.t<<",\"head\":"<<c.h<<",\"pc\":"<<s.pc<<",\"gap\":"<<x[m]-c.h-48<<",\"edits\":[";
 for(int j=0;j<(int)edits.size();j++){auto e=edits[j];if(j)cout<<',';cout<<"["<<e.id<<','<<e.q<<','<<e.b<<','<<e.a.w<<','<<e.a.d<<','<<e.a.n<<"]";}cout<<"],\"values\":[";
 for(int j=0;j<(int)v.size();j++){if(j)cout<<',';cout<<v[j];}cout<<"],\"ones\":[";for(int j=0;j<(int)x.size();j++){if(j)cout<<',';cout<<x[j];}cout<<"]}"<<endl;return true;
 }
 return false;
}
void run(C c){
 nodes++;if(nodes%1000==0)cerr<<"nodes "<<nodes<<" leaves "<<leaves<<" steps "<<steps<<" hits "<<successes<<" depth "<<edits.size()<<" start "<<startq<<endl;
 if(nodes>=cap)return;
 vector<int>marked; C origin=c; unordered_map<unsigned long long,int> seen;
 while(true){
  if(!ex[c.q]){halts++;break;}
  if(frame(c))break;
  if(c.t>=bound||abs(c.h)>20000||c.ones.size()>20000){limits++;break;}
  unsigned long long hh=c.th^mix(0x100000000ULL+c.q)^mix(0x200000000ULL+(unsigned long long)(long long)c.h);
  auto ss=seen.find(hh);
  if(ss!=seen.end()){
   C old=origin;while(old.t<ss->second){int bb=old.ones.count(old.h);A a=row[old.q][bb];if(a.w)old.ones.insert(old.h);else old.ones.erase(old.h);old.h+=a.d;old.q=a.n;old.t++;}
   if(old.q==c.q&&old.h==c.h&&old.ones==c.ones){cycles++;break;}
  }
  seen[hh]=c.t;
  int b=c.ones.count(c.h),key=c.q*2+b;
  if(!decided[key]&&!opts[key].empty()&&(int)edits.size()<budget){
   decided[key]=true;marked.push_back(key);
   // Changed branches first; the unchanged branch continues in-place.
   for(E e:opts[key]){row[e.q][e.b]=e.a;edits.push_back(e);run(c);edits.pop_back();if(nodes>=cap)break;}
   row[c.q][b]=base[c.q][b];
   if(nodes>=cap)break;
  }
  if(!b&&(c.ones.empty()||c.h<*c.ones.begin()||c.h>*c.ones.rbegin())&&ray(c.q,c.h,c.ones)){rays++;break;}
  A a=row[c.q][b];if(a.w!=b)c.th^=mix((unsigned long long)(long long)c.h);if(a.w)c.ones.insert(c.h);else c.ones.erase(c.h);c.h+=a.d;c.q=a.n;c.t++;steps++;
 }
 leaves++;for(int key:marked)decided[key]=false;
}
int main(int argc,char**argv){if(argc<6){cerr<<"table edits seeds budget maxsteps [start or all] [cap]\n";return 2;}
 ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]={w,d=='R'?1:-1,n};}row=base;
 ifstream ef(argv[2]);E e;while(ef>>e.id>>e.q>>e.b>>e.a.w>>e.a.d>>e.a.n)opts[e.q*2+e.b].push_back(e);
 ifstream sf(argv[3]);Seed s;while(sf>>s.pc>>s.path>>s.arb)seeds.push_back(s);
 budget=stoi(argv[4]);bound=stoi(argv[5]);string init=argc>6?argv[6]:"74";if(argc>7)cap=stoll(argv[7]);
 auto t=chrono::steady_clock::now();vector<int> starts=init=="all"?qs:vector<int>{stoi(init)};
 for(int q:starts){startq=q;run({q,0,0,{}});if(nodes>=cap)break;}
 cerr<<"DONE nodes "<<nodes<<" leaves "<<leaves<<" steps "<<steps<<" successes "<<successes<<" rays "<<rays<<" halts "<<halts<<" limits "<<limits<<" cycles "<<cycles<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t).count()<<endl;
}
