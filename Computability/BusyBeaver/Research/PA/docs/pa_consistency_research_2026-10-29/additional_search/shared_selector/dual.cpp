// Exploratory coupled folds sharing one context selector, sample screening only.
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <cstdint>
using namespace std;struct Tr{int w,d,z;};Tr tab[1000][2];bool ex[1000];vector<uint64_t>ctx[1000][2];
struct Fold{int a,b,c;};vector<Fold>fs;Fold f,g;int h;Tr rep[2];
uint64_t rng=34165743813UL;uint64_t rnd(){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
int proj(int q){return q==f.a?f.b:q==g.a?g.b:q;}
uint64_t wr(uint64_t t,int i,int w){return(t&~(1ULL<<i))|(uint64_t(w)<<i);}
bool test(int oq,uint64_t before,int known){
 int b=(before>>32)&1;Tr a=tab[oq][b];int es=proj(a.z),eh=32+a.d;uint64_t expected=wr(before,32,a.w);
 // The common representative performs its new L-selector row first.
 int q=h,pos=31;uint64_t tape=before;
 for(int k=1;k<31;k++){
  if(q==254||pos<0||pos>63)return false;
  int bit=(tape>>pos)&1;Tr a;
  if(q==h){if(known>=0&&bit!=known)return false;a=rep[bit];}
  else if((q==f.b&&bit==f.c)||(q==g.b&&bit==g.c))a={bit,-1,h};
  else{a=tab[q][bit];a.z=proj(a.z);}
  tape=wr(tape,pos,a.w);pos+=a.d;q=a.z;
  if(q==es&&pos==eh&&tape==expected)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=5)return 1;ifstream ti(argv[1]);string line;while(getline(ti,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream s(line);s>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};ex[q]=true;}
 ifstream ci(argv[2]);int q,c;while(ci>>q>>c){uint64_t known=uint64_t(c)<<27;int b=(c>>5)&1;ctx[q][b].push_back(known);ctx[q][b].push_back(known|(rnd()&~(2047ULL<<27)));}
 ifstream fi(argv[3]);Fold a;while(fi>>a.a>>a.b>>a.c)fs.push_back(a);vector<int>states;for(int q=0;q<1000;q++)if(ex[q])states.push_back(q);
 ofstream out(argv[4]);int count=0;
 for(int i=0;i<(int)fs.size();i++)for(int j=i+1;j<(int)fs.size();j++){
  f=fs[i];g=fs[j];if(f.a==g.a||f.a==g.b||f.b==g.a||f.b==g.b)continue;h=f.a;
  vector<Tr>options[2];
  for(int marker=0;marker<2;marker++)for(int z:states){if(z==g.a)continue;for(int d:{-1,1})for(int w:{0,1}){
   rep[marker]={w,d,z};bool ok=true;
   for(Fold p:{f,g}){int q=marker?p.b:p.a;for(uint64_t t:ctx[q][p.c])if(!test(q,t,marker)){ok=false;break;}if(!ok)break;}
   if(ok)options[marker].push_back(rep[marker]);
  }}
  if(!options[0].empty()&&!options[1].empty()){
   for(Tr a:options[0])for(Tr b:options[1]){rep[0]=a;rep[1]=b;bool ok=true;
    for(Fold p:{f,g})for(int q:{p.a,p.b}){for(uint64_t t:ctx[q][p.c])if(!test(q,t,-1)){ok=false;break;}if(!ok)break;}
    if(ok){count++;out<<f.a<<' '<<f.b<<' '<<f.c<<' '<<g.a<<' '<<g.b<<' '<<g.c<<' '<<a.w<<' '<<a.d<<' '<<a.z<<' '<<b.w<<' '<<b.d<<' '<<b.z<<'\n';cout<<"FOUND "<<f.a<<','<<f.b<<' '<<g.a<<','<<g.b<<endl;}
   }
  }
 }
 cout<<"DONE "<<count<<endl;
}
