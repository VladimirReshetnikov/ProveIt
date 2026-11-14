// Bounded exploration only. This excludes no other initialization method.
#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;};
struct E {int id,q,b;A a;};
int main(int ac,char**av){if(ac<5){cerr<<"table pool templates bound [start] [lo] [hi]\n";return 2;}
 int bound=stoi(av[4]),onlystart=ac>5?stoi(av[5]):-1,lo=ac>6?stoi(av[6]):0,hi=ac>7?stoi(av[7]):INT_MAX;
 A row[3000][2],base[3000][2];bool ex[3000]={};vector<int>qs;ifstream tf(av[1]);int q,b,w,n;char d;
 while(tf>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=1;row[q][b]=base[q][b]={w,d=='R'?1:-1,n};}
 vector<E>es;ifstream ef(av[2]);E e;while(ef>>e.id>>e.q>>e.b>>e.a.w>>e.a.d>>e.a.n)es.push_back(e);
 map<unsigned long long,int>seeds;ifstream sf(av[3]);int pc,ar;string path;while(sf>>pc>>path>>ar){unsigned long long v=0;for(int i=0;i<(int)path.size();i++)if(path[i]=='1')v|=1ULL<<i;seeds[v]=pc;}
 struct Snap {int start,q,h,steps;set<int> ones;};
 vector<vector<Snap>> prefixes;
 if(onlystart<0)for(int start:qs){vector<Snap> hist;set<int>ones;int q=start,h=0;bool terminal=false;
  for(int st=0;st<1000;st++){if(!ex[q]){terminal=true;break;}hist.push_back({start,q,h,st,ones});int b=ones.count(h);A a=base[q][b];
   if(!b&&a.n==q&&((a.d==1&&(ones.empty()||h>*ones.rbegin()))||(a.d==-1&&(ones.empty()||h<*ones.begin())))){terminal=true;break;}
   if(a.w)ones.insert(h);else ones.erase(h);h+=a.d;q=a.n;}
  if(!terminal)throw runtime_error("Unclassified original blank prefix");prefixes.push_back(hist);
 }
 long long sims=0,ticks=0,halts=0,rays=0,limits=0,frames=0,classified=0;int pairid=0;vector<int>starts=onlystart>=0?vector<int>{onlystart}:qs;auto t0=chrono::steady_clock::now();
 for(int i=0;i<(int)es.size();i++)for(int j=i+1;j<(int)es.size();j++){E ei=es[i],ej=es[j];if(ei.q==ej.q&&ei.b==ej.b)continue;int pid=pairid++;if(pid<lo||pid>=hi)continue;
  row[ei.q][ei.b]=ei.a;row[ej.q][ej.b]=ej.a;
  int rd[3000]={};
  for(int q:qs){int r=q,di=0;set<int>seen;while(ex[r]&&!seen.count(r)){seen.insert(r);A a=row[r][0];if(di&&di!=a.d){di=0;break;}di=a.d;r=a.n;}if(di&&seen.count(r))rd[q]=di;}
  vector<Snap> reps;
  if(onlystart>=0)reps.push_back({onlystart,onlystart,0,0,{}});
  else{set<vector<int>> sigs;
   for(auto& hist:prefixes){bool hit=false;for(auto sn:hist){int bit=sn.ones.count(sn.h);if((sn.q==ei.q&&bit==ei.b)||(sn.q==ej.q&&bit==ej.b)){
    vector<int>sig{sn.q};for(int p:sn.ones)sig.push_back(p-sn.h);hit=true;
    if(sigs.insert(sig).second){set<int>rel;for(int p:sn.ones)rel.insert(p-sn.h);sn.ones=rel;reps.push_back(sn);}break;}}
    if(!hit)classified++;
   }
  }
  for(auto sn:reps){int start=sn.start;sims++;int q=sn.q,h=0;set<int>ones=sn.ones;bool touchedA=false,touchedB=false;for(int st=0;st<=bound;st++){
   if(!ex[q]){halts++;break;}
   if(q==84&&ones.size()>=13&&*ones.begin()==h-1){auto it=next(ones.begin());unsigned long long mask=0;while(it!=ones.end()&&*it<h+48){int off=*it-h;if(off<0)break;mask|=1ULL<<off;++it;}if(it!=ones.end()&&*it>=h+48&&seeds.count(mask)){
    bool ok=true;int pos=*it++,gap=pos-h-48;vector<int>values;while(it!=ones.end()){if(*it!=pos+2){ok=false;break;}int len=1;pos=*it++;while(it!=ones.end()&&*it==pos+1){len++;pos=*it++;}values.push_back(len-1);}if(ok&&values.size()>=10){frames++;cout<<"{\"pair\":"<<pid<<",\"edit_ids\":["<<ei.id<<","<<ej.id<<"],\"start\":"<<start<<",\"steps\":"<<(st+sn.steps)<<",\"head\":"<<(h+sn.h)<<",\"pc\":"<<seeds[mask]<<",\"gap\":"<<gap<<",\"values\":[";for(int k=0;k<(int)values.size();k++){if(k)cout<<',';cout<<values[k];}cout<<"],\"ones\":[";bool fi=true;for(int p:ones){if(!fi)cout<<',';fi=false;cout<<(p+sn.h);}cout<<"]}"<<endl;break;}
   }}
   if(st==bound||abs(h)>20000||ones.size()>20000){limits++;break;}
   int bit=ones.count(h);if(!bit&&rd[q]&&((rd[q]==1&&(ones.empty()||*ones.rbegin()<h))||(rd[q]==-1&&(ones.empty()||*ones.begin()>h)))){rays++;break;}
   if(q==ei.q&&bit==ei.b)touchedA=true;if(q==ej.q&&bit==ej.b)touchedB=true;
   A a=row[q][bit];if(a.w)ones.insert(h);else ones.erase(h);h+=a.d;q=a.n;ticks++;
  }}
  row[ei.q][ei.b]=base[ei.q][ei.b];row[ej.q][ej.b]=base[ej.q][ej.b];
  if(pid%1000==0)cerr<<"PAIR "<<pid<<" sims "<<sims<<" ticks "<<ticks<<" frames "<<frames<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
 }
 cerr<<"DONE pairs "<<pairid<<" skipped_unchanged "<<classified<<" simulations "<<sims<<" ticks "<<ticks<<" frames "<<frames<<" halts "<<halts<<" rays "<<rays<<" limits "<<limits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
}
