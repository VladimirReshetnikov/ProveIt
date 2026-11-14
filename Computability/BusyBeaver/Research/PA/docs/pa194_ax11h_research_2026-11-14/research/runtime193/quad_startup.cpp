#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;};
struct Edit{int id,q,b; A a;};
struct Seed{int pc;string path;int arbitrary;};
constexpr int WIDTH=50001,OFF=25000;
array<A,2> base[3000],row[3000];
vector<int> qs; bool ex[3000]{}; vector<Edit> es;vector<Seed> seeds;
long long ticks=0,runs=0,hits=0,limits=0,halts=0,rays=0;
int BOUND=200000;
int simulate(int start,int e1,int e2,bitset<6000>*used=nullptr){
 static unsigned char tape[WIDTH];memset(tape,0,WIDTH);
 int h=OFF,q=start,mi=OFF,ma=OFF,ones=0;
 int edmask=0;
 runs++;
 for(int st=0;st<=BOUND;st++){
  if(q==254){halts++;return 0;}
  if(st==BOUND||h<100||h>=WIDTH-100||ones>20000){limits++;return 0;}
  if(q==84&&ones>=13){
   while(mi<=ma&&!tape[mi])mi++;while(ma>=mi&&!tape[ma])ma--;
   if(mi==h-1){for(auto &seed:seeds){
    bool ok=true;int p=h;
    for(char c:seed.path){if(tape[p++]!=c-'0'){ok=false;break;}}
    if(!ok)continue;
    while(p<=ma&&!tape[p])p++;
    if(p<h+36||p>ma)continue;
    int header=p;vector<int>values;
    while(p<ma){
     if(tape[++p]||!tape[++p]){ok=false;break;}
     int len=0;while(tape[p]){len++;p++;}
     values.push_back(len-1);p--;
    }
    if(!ok||values.size()<10)continue;
    hits++;
    cout<<"{\"edits\":["<<e1<<","<<e2<<"],\"start\":"<<start<<",\"steps\":"<<st<<",\"head\":"<<h-OFF<<",\"pc\":"<<seed.pc<<",\"gap\":"<<header-h-36<<",\"values\":[";
    for(size_t j=0;j<values.size();j++){if(j)cout<<',';cout<<values[j];}cout<<"],\"ones\":[";
    bool first=true;for(int j=mi;j<=ma;j++)if(tape[j]){if(!first)cout<<',';first=false;cout<<j-OFF;}cout<<"]}"<<endl;
    return 1;
   }}
  }
  int b=tape[h];if(used)(*used)[2*q+b]=true;
  auto a=row[q][b];
  if(!b&&a.n==q&&((a.d==1&&h>ma)||(a.d==-1&&h<mi)||!ones)){rays++;return 0;}
  if(a.w!=b){ones+=a.w-b;tape[h]=a.w;if(a.w){mi=min(mi,h);ma=max(ma,h);}}
  h+=a.d;q=a.n;ticks++;
 }
 return 0;
}
int main(int argc,char**argv){
 if(argc<5)return 2;
 if(argc>5)BOUND=atoi(argv[5]);
 ifstream f(argv[1]);int q,b,w,n;char dir;
 while(f>>q>>b>>w>>dir>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]={w,dir=='R'?1:-1,n};}
 ifstream ef(argv[2]);Edit e;while(ef>>e.id>>e.q>>e.b>>e.a.w>>e.a.d>>e.a.n)es.push_back(e);
 ifstream sf(argv[3]);Seed s;while(sf>>s.pc>>s.path>>s.arbitrary)seeds.push_back(s);
 int stage=atoi(argv[4]);
 for(int q:qs)row[q]=base[q];
 vector<bitset<6000>> baseline(qs.size());
 for(size_t j=0;j<qs.size();j++)simulate(qs[j],-1,-1,&baseline[j]);
 vector<vector<bitset<6000>>> single(es.size(),vector<bitset<6000>>(qs.size()));
 for(size_t i=0;i<es.size();i++){
  auto a=es[i];row[a.q][a.b]=a.a;
  for(size_t j=0;j<qs.size();j++){
   if(baseline[j][2*a.q+a.b])simulate(qs[j],i,-1,&single[i][j]);else single[i][j]=baseline[j];
  }
  row[a.q][a.b]=base[a.q][a.b];
 }
 cerr<<"SINGLES runs "<<runs<<" ticks "<<ticks<<" hits "<<hits<<" limits "<<limits<<endl;
 long long eligible=0,triples=0,quads=0;unordered_set<unsigned long long> done3,done4;
 auto t0=chrono::steady_clock::now();
 for(size_t i=0;i<es.size();i++){
  auto a=es[i];row[a.q][a.b]=a.a;
  for(size_t k=i+1;k<es.size();k++){
   auto c=es[k];if(a.q==c.q&&a.b==c.b)continue;row[c.q][c.b]=c.a;
   for(size_t j=0;j<qs.size();j++){
    if((stage==1||stage==3||stage==5)&&qs[j]!=74)continue;
    bool eligible1=baseline[j][2*a.q+a.b]&&single[i][j][2*c.q+c.b];
    bool eligible2=baseline[j][2*c.q+c.b]&&single[k][j][2*a.q+a.b];
    if(eligible1||eligible2){
     eligible++;bitset<6000> pairused;simulate(qs[j],i,k,stage>=3?&pairused:nullptr);
     if(stage>=3)for(size_t z=0;z<es.size();z++){
      auto d=es[z];if(z==i||z==k||(d.q==a.q&&d.b==a.b)||(d.q==c.q&&d.b==c.b)||!pairused[2*d.q+d.b])continue;
      array<size_t,3> ids{i,k,z};sort(ids.begin(),ids.end());
      unsigned long long tag=(((ids[0]*es.size()+ids[1])*es.size()+ids[2])*qs.size()+j);
      if(!done3.insert(tag).second)continue;
      row[d.q][d.b]=d.a;triples++;bitset<6000> tripleused;int hit=simulate(qs[j],i,k,stage>=5?&tripleused:nullptr);
      if(stage>=5)for(size_t v=0;v<es.size();v++){
       auto e=es[v]; if(v==i||v==k||v==z||(e.q==a.q&&e.b==a.b)||(e.q==c.q&&e.b==c.b)||(e.q==d.q&&e.b==d.b)||!tripleused[2*e.q+e.b])continue;
       array<size_t,4> ids4{i,k,z,v};sort(ids4.begin(),ids4.end());
       unsigned long long tag4=((((ids4[0]*es.size()+ids4[1])*es.size()+ids4[2])*es.size()+ids4[3])*qs.size()+j);
       if(!done4.insert(tag4).second)continue;
       row[e.q][e.b]=e.a; quads++; int hit4=simulate(qs[j],i,k);
       if(hit4)cerr<<"QUAD_HIT edits "<<i<<" "<<k<<" "<<z<<" "<<v<<" start "<<qs[j]<<endl;
       row[e.q][e.b]=base[e.q][e.b];
      }
      if(hit)cerr<<"TRIPLE_HIT edits "<<i<<" "<<k<<" "<<z<<" start "<<qs[j]<<endl;
      row[d.q][d.b]=base[d.q][d.b];
     }
    }
   }
   row[c.q][c.b]=base[c.q][c.b];
  }
  row[a.q][a.b]=base[a.q][a.b];
  if(i%10==0)cerr<<"PAIR "<<i<<" runs "<<runs<<" ticks "<<ticks<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;
 }
 cerr<<"DONE eligible "<<eligible<<" quads "<<quads<<" triples "<<triples<<" runs "<<runs<<" ticks "<<ticks<<" hits "<<hits<<" limits "<<limits<<" halts "<<halts<<" rays "<<rays<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;
}
