#include <bits/stdc++.h>
using namespace std;
struct Act {int w,d,n;};
struct Edit {int id,q,b; Act a;};
struct Seed {int pc; string path; int any;};
array<Act,2> base[3000], row[3000];
bool exists_[3000];
int raymemo[2][3000];
int ray(int q,int dd) {
  int &v=raymemo[dd][q];
  if(v>=0)return v==1 || v==2;
  if(!exists_[q] || row[q][0].d!=(dd?1:-1))return v=0;
  v=2;
  return v=ray(row[q][0].n,dd);
}
int main(int argc,char**argv) {
 if(argc<6){cerr<<"table edits seeds maxSteps start(-1=all) [lo hi]\n";return 2;}
 vector<int> qs; ifstream f(argv[1]); int q,b,w,n; char d;
 while(f>>q>>b>>w>>d>>n){if(!exists_[q])qs.push_back(q);exists_[q]=1;base[q][b]={w,d=='R'?1:-1,n};}
 vector<Edit> edits; ifstream e(argv[2]); Edit ed; while(e>>ed.id>>ed.q>>ed.b>>ed.a.w>>ed.a.d>>ed.a.n)edits.push_back(ed);
 vector<Seed> seeds; ifstream sf(argv[3]);Seed s;while(sf>>s.pc>>s.path>>s.any)seeds.push_back(s);
 int bound=stoi(argv[4]),only=stoi(argv[5]),lo=argc>6?stoi(argv[6]):0,hi=argc>7?stoi(argv[7]):edits.size();
 vector<int> starts=only<0?qs:vector<int>{only};
 long long simulations=0,ticks=0,halts=0,rays=0,limits=0,successes=0,pairs=0;
 auto t0=chrono::steady_clock::now();
 for(size_t i=lo;i<edits.size() && (int)i<hi;i++)for(size_t j=i+1;j<edits.size();j++) {
  auto a=edits[i],c=edits[j];if(a.q==c.q&&a.b==c.b)continue;
  for(int q:qs)row[q]=base[q];row[a.q][a.b]=a.a;row[c.q][c.b]=c.a;
  memset(raymemo,-1,sizeof(raymemo));for(int q:qs){ray(q,0);ray(q,1);}
  pairs++;
  for(int start:starts){simulations++;q=start;int h=0;set<int>ones;
   for(int st=0;st<=bound;st++) {
    if(q==254 || !exists_[q]){halts++;break;}
    if(q==84&&ones.size()>=13){
     vector<int>x(ones.begin(),ones.end());
     for(auto &seed:seeds){
      vector<int>pre{h-1};for(size_t k=0;k<seed.path.size();k++)if(seed.path[k]=='1')pre.push_back(h+k);
      size_t m=pre.size();bool ok=x.size()>m&&equal(pre.begin(),pre.end(),x.begin())&&x[m]>=h+48;
      if(!ok)continue;
      vector<int>vals;size_t k=m+1;int pos=x[m];
      while(ok&&k<x.size()){if(x[k]!=pos+2){ok=false;break;}int len=1;pos=x[k++];while(k<x.size()&&x[k]==pos+1){len++;pos=x[k++];}vals.push_back(len-1);}
      if(vals.size()<10)ok=false;
      if(ok){successes++;cout<<"{\"edits\":["<<i<<","<<j<<"],\"start\":"<<start<<",\"steps\":"<<st<<",\"head\":"<<h<<",\"pc\":"<<seed.pc<<",\"values\":[";
       for(size_t k=0;k<vals.size();k++){if(k)cout<<',';cout<<vals[k];}cout<<"],\"ones\":[";for(size_t k=0;k<x.size();k++){if(k)cout<<',';cout<<x[k];}cout<<"]}"<<endl;goto done;
      }
     }
    }
    if(st==bound||abs(h)>20000||ones.size()>20000){limits++;break;}
    bool bit=ones.count(h);if(!bit){bool empty=ones.empty();if((raymemo[1][q]&&(empty||*ones.rbegin()<h))||(raymemo[0][q]&&(empty||*ones.begin()>h))){rays++;break;}}
    Act ac=row[q][bit];if(ac.w)ones.insert(h);else ones.erase(h);h+=ac.d;q=ac.n;ticks++;
   }
   done:;
  }
  if(j+1==edits.size())cerr<<"i "<<i<<" pairs "<<pairs<<" sims "<<simulations<<" ticks "<<ticks<<" successes "<<successes<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;
 }
 cerr<<"DONE pairs "<<pairs<<" sims "<<simulations<<" ticks "<<ticks<<" halts "<<halts<<" rays "<<rays<<" limits "<<limits<<" successes "<<successes<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;
}
