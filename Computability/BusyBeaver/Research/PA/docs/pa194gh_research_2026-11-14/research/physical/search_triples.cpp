#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};struct Edit{int id,q,b,w,d,n;};struct Seed{int pc;string path;int arbitrary;};
int main(int argc,char**argv){if(argc<5){cerr<<"table edits seeds bound\n";return 2;}
 array<A,2>base[3000],row[3000];bool ex[3000]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]={w,d=='R'?1:-1,n};}for(int q:qs)row[q]=base[q];
 vector<Edit>es;Edit ed;ifstream ef(argv[2]);while(ef>>ed.id>>ed.q>>ed.b>>ed.w>>ed.d>>ed.n)es.push_back(ed);
 vector<Seed>ss;Seed s;ifstream sf(argv[3]);while(sf>>s.pc>>s.path>>s.arbitrary)ss.push_back(s);int bound=stoi(argv[4]);
 // Baseline prefix reaches its permanent state35 writing ray at time92.
 set<pair<int,int>>initial;{int q=74,h=0;set<int>ones;for(int st=0;st<93;st++){int bit=ones.count(h);initial.insert({q,bit});A x=base[q][bit];if(x.w)ones.insert(h);else ones.erase(h);h+=x.d;q=x.n;}if(q!=35)throw runtime_error("baseline ray");}
 vector<bool>active;for(Edit e:es)active.push_back(initial.count({e.q,e.b}));
 long triples=0,skip=0,simulations=0,ticks=0,rays=0,halts=0,limits=0,cycles=0,hits=0;auto t0=chrono::steady_clock::now();
 for(int i=0;i<(int)es.size();i++)for(int j=i+1;j<(int)es.size();j++)for(int k=j+1;k<(int)es.size();k++){
  Edit a=es[i],b=es[j],c=es[k];if((a.q==b.q&&a.b==b.b)||(a.q==c.q&&a.b==c.b)||(b.q==c.q&&b.b==c.b))continue;
  triples++;if(!active[i]&&!active[j]&&!active[k]){skip++;continue;}simulations++;
  row[a.q][a.b]={a.w,a.d,a.n};row[b.q][b.b]={b.w,b.d,b.n};row[c.q][c.b]={c.w,c.d,c.n};
  int q=74,h=0,pow=1,lam=0,cq=74,ch=0;set<int>ones,checkpoint;int raycache[3000];fill(raycache,raycache+3000,2);
  for(int st=0;st<=bound;st++){
   if(q==254){halts++;break;}
   bool found=false;
   if(q==84&&ones.size()>=13)for(Seed seed:ss){vector<int>x(ones.begin(),ones.end()),prefix{h-1};for(int z=0;z<(int)seed.path.size();z++)if(seed.path[z]=='1')prefix.push_back(h+z);size_t m=prefix.size();bool ok=x.size()>m&&equal(prefix.begin(),prefix.end(),x.begin())&&x[m]>=h+48;if(!ok)continue;int gap=x[m]-h-48,pos=x[m];size_t z=m+1;vector<int>vs;while(ok&&z<x.size()){if(x[z]!=pos+2){ok=false;break;}int len=1;pos=x[z++];while(z<x.size()&&x[z]==pos+1){len++;pos=x[z++];}vs.push_back(len-1);}if(vs.size()<10)ok=false;if(ok){hits++;cout<<"{\"edits\":["<<a.id<<','<<b.id<<','<<c.id<<"],\"start\":74,\"steps\":"<<st<<",\"pc\":"<<seed.pc<<",\"head\":"<<h<<",\"gap\":"<<gap<<",\"values\":[";for(size_t z=0;z<vs.size();z++){if(z)cout<<',';cout<<vs[z];}cout<<"]}"<<endl;found=true;break;}}
   if(found)break;
   if(st==bound||abs(h)>20000||ones.size()>20000){limits++;break;}
   if(st&&q==cq&&h==ch&&ones==checkpoint){cycles++;break;}
   if(lam==pow){cq=q;ch=h;checkpoint=ones;pow*=2;lam=0;}lam++;
   bool bit=ones.count(h);
   if(!bit&&(ones.empty()||h<*ones.begin()||h>*ones.rbegin())){
    if(raycache[q]==2){int r=q,dr=0;set<int>seen;while(r>=0&&r<3000&&ex[r]&&!seen.count(r)){seen.insert(r);A x=row[r][0];if(dr&&x.d!=dr){dr=0;break;}dr=x.d;r=x.n;}raycache[q]=(dr&&seen.count(r))?dr:0;}
    int rd=raycache[q];if(rd&&((rd==1&&(ones.empty()||*ones.rbegin()<h))||(rd==-1&&(ones.empty()||*ones.begin()>h)))){rays++;break;}
   }
   A act=row[q][bit];if(act.w)ones.insert(h);else ones.erase(h);h+=act.d;q=act.n;ticks++;
  }
  row[a.q][a.b]=base[a.q][a.b];row[b.q][b.b]=base[b.q][b.b];row[c.q][c.b]=base[c.q][c.b];
  if(simulations%100000==0)cerr<<"PROGRESS triples "<<triples<<" simulations "<<simulations<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
 }
 cerr<<"DONE triples "<<triples<<" skipped_unchanged_prefix "<<skip<<" simulations "<<simulations<<" ticks "<<ticks<<" hits "<<hits<<" rays "<<rays<<" halts "<<halts<<" cycles "<<cycles<<" limits "<<limits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
}
