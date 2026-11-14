// Joint two-row neutral-rewrite bootstrap search for the inherited runtime193 core.
#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;};
struct Edit {int id,q,b,w,d,n;};
struct Seed {int pc;string path;int arbitrary;};
int main(int argc,char**argv) {
 if(argc<6) {cerr<<"table edits seeds bound all_starts [start_pair end_pair]\n";return 2;}
 vector<int> qs; array<A,2> base[3000],row[3000]; bool ex[3000]={};
 ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]={w,d=='R'?1:-1,n};}
 vector<Edit> edits;ifstream ef(argv[2]);Edit ed;
 while(ef>>ed.id>>ed.q>>ed.b>>ed.w>>ed.d>>ed.n)edits.push_back(ed);
 vector<Seed> seeds;ifstream sf(argv[3]);Seed ss;while(sf>>ss.pc>>ss.path>>ss.arbitrary)seeds.push_back(ss);
 int bound=stoi(argv[4]),allstarts=stoi(argv[5]);long lo=argc>6?stol(argv[6]):0,hi=argc>7?stol(argv[7]):LONG_MAX;
 long pairid=0,simulations=0,ticks=0,halts=0,rays=0,limits=0,hits=0,cycles=0;
 vector<int>starts=allstarts?qs:vector<int>{74};
 auto t0=chrono::steady_clock::now();
 for(int i=0;i<(int)edits.size();i++)for(int j=i+1;j<(int)edits.size();j++) {
  Edit a=edits[i],b=edits[j]; if(a.q==b.q&&a.b==b.b)continue;
  long id=pairid++;if(id<lo||id>=hi)continue;
  for(int q:qs)row[q]=base[q];row[a.q][a.b]={a.w,a.d,a.n};row[b.q][b.b]={b.w,b.d,b.n};
  int raydir[3000]={};
  for(int q:qs){int r=q,dr=0;set<int>seen;
   while(r>=0&&r<3000&&ex[r]&&!seen.count(r)){seen.insert(r);A x=row[r][0];if(dr&&x.d!=dr){dr=0;break;}dr=x.d;r=x.n;}
   if(dr&&seen.count(r))raydir[q]=dr;
  }
  for(int start:starts){simulations++;int q=start,h=0;set<int>ones, checkpoint;bool ended=false;int cq=start,ch=0,power=1,lambda=0;
   for(int st=0;st<=bound;st++){
    if(q==254){halts++;ended=true;break;}
    if(q==84&&ones.size()>=13)for(Seed seed:seeds){
     vector<int>x(ones.begin(),ones.end()),prefix{h-1};for(size_t z=0;z<seed.path.size();z++)if(seed.path[z]=='1')prefix.push_back(h+z);
     size_t m=prefix.size();bool ok=x.size()>m&&equal(prefix.begin(),prefix.end(),x.begin())&&x[m]>=h+48;
     if(!ok)continue;int gap=x[m]-h-48,pos=x[m];vector<int>values;size_t k=m+1;
     while(ok&&k<x.size()){if(x[k]!=pos+2){ok=false;break;}int len=1;pos=x[k++];while(k<x.size()&&x[k]==pos+1){len++;pos=x[k++];}values.push_back(len-1);}
     if(values.size()<10)ok=false;
     if(ok){hits++;cout<<"{\"pair\":"<<id<<",\"edits\":["<<a.id<<","<<b.id<<"],\"start\":"<<start<<",\"steps\":"<<st<<",\"head\":"<<h<<",\"pc\":"<<seed.pc<<",\"gap\":"<<gap<<",\"values\":[";for(size_t k=0;k<values.size();k++){if(k)cout<<',';cout<<values[k];}cout<<"],\"ones\":[";for(size_t k=0;k<x.size();k++){if(k)cout<<',';cout<<x[k];}cout<<"]}"<<endl;ended=true;break;}
    }
    if(ended)break;
    if(st && q==cq && h==ch && ones==checkpoint){cycles++;ended=true;break;}
    if(lambda==power){cq=q;ch=h;checkpoint=ones;power*=2;lambda=0;}lambda++;
    if(st==bound||abs(h)>20000||ones.size()>20000){limits++;ended=true;break;}
    bool bit=ones.count(h);int rd=raydir[q];
    if(!bit&&rd&&((rd==1&&(ones.empty()||*ones.rbegin()<h))||(rd==-1&&(ones.empty()||*ones.begin()>h)))){rays++;ended=true;break;}
    A act=row[q][bit];if(act.w)ones.insert(h);else ones.erase(h);h+=act.d;q=act.n;ticks++;
   }
  }
  if(id%500==0)cerr<<"PROGRESS pair "<<id<<" simulations "<<simulations<<" ticks "<<ticks<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
 }
 cerr<<"DONE pairs "<<pairid<<" simulations "<<simulations<<" ticks "<<ticks<<" hits "<<hits<<" rays "<<rays<<" halts "<<halts<<" cycles "<<cycles<<" limits "<<limits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
}
