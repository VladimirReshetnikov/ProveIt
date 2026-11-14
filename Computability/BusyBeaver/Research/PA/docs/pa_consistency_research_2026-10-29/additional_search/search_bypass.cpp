// Finite-context candidate synthesis; every result needs a universal proof.
#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <iostream>
#include <cstdint>
using namespace std;
struct Tr{int w,d,z;};Tr tab[1000][2];bool exists[1000];vector<uint64_t>ctx[1000][2];
uint64_t rng=8337146137873UL;uint64_t rand64(){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
uint64_t write(uint64_t t,int h,int w){return (t&~(1ULL<<h))|(uint64_t(w)<<h);}
bool check(int p,int b,int q,Tr first,uint64_t before){
 Tr old=tab[p][b];uint64_t exp=write(before,32,old.w);int eh=32+old.d;Tr old2=tab[q][(exp>>eh)&1];exp=write(exp,eh,old2.w);eh+=old2.d;int es=old2.z;
 uint64_t act=write(before,32,first.w);int h=32+first.d,s=first.z;
 for(int k=0;k<32;k++){
  if(s==es&&h==eh&&act==exp)return true;
  if(s==254||s==q||h<0||h>63)return false;
  Tr a=tab[s][(act>>h)&1];act=write(act,h,a.w);h+=a.d;s=a.z;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=4)return 1;ifstream in(argv[1]);string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream ss(line);ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};exists[q]=true;}
 ifstream ct(argv[2]);int p,code;while(ct>>p>>code){uint64_t known=uint64_t(code)<<27;int b=(code>>5)&1;ctx[p][b].push_back(known);ctx[p][b].push_back(known|(rand64()&~(2047ULL<<27)));}
 vector<int>st;for(int q=0;q<1000;q++)if(exists[q])st.push_back(q);
 ofstream out(argv[3]);int full=0;
 for(int q:st){if(q==0||q==84||tab[q][0].z==q||tab[q][1].z==q)continue;
  bool complete=true;int incoming=0,passed=0;ostringstream bundle;
  for(int p:st)for(int b:{0,1})if(tab[p][b].z==q){incoming++;vector<Tr>opts;
   for(int r:st)if(r!=q)for(int d:{-1,1})for(int w:{0,1}){
    Tr candidate={w,d,r};bool ok=true;
    for(uint64_t c:ctx[p][b])if(!check(p,b,q,candidate,c)){ok=false;break;}
    if(ok)opts.push_back(candidate);
   }
   if(opts.empty())complete=false;else{
    passed++;bundle<<q<<' '<<p<<' '<<b;for(Tr a:opts)bundle<<' '<<a.w<<','<<a.d<<','<<a.z;bundle<<'\n';
   }
  }
  if(passed){cout<<"STATE "<<q<<" "<<passed<<"/"<<incoming<<endl;out<<bundle.str();}
  if(complete){full++;cout<<"COMPLETE "<<q<<endl;}
 }
 cout<<"DONE "<<full<<endl;
}
