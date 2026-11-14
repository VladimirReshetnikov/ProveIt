// Exploratory finite-context screening only: acceptance is not a proof.
#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <iostream>
#include <cstdint>
using namespace std;
struct Tr {int w,d,z;};
Tr tab[1000][2];bool exists[1000];
vector<uint64_t> ctx[1000][2];
uint64_t rng=721209836421UL;
uint64_t random64(){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
int dropq,keepq,cb;Tr rep;
int project(int z){return z==dropq?keepq:z;}
bool check(int q,uint64_t before,int limit){
 int b=(before>>32)&1;Tr old=tab[q][b];int es=project(old.z),eh=32+old.d;
 uint64_t expected=(before & ~(1ULL<<32))|(uint64_t(old.w)<<32);
 int s=keepq,h=32;uint64_t a=before;
 for(int i=0;i<limit;i++){
  if(s==254 || h<0 || h>63)return false;
  int bit=(a>>h)&1;Tr t=(s==keepq && bit==cb)?rep:tab[s][bit];
  a=(a & ~(1ULL<<h))|(uint64_t(t.w)<<h);h+=t.d;s=project(t.z);
  if(s==es && h==eh && a==expected)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=4)return 1;ifstream in(argv[1]);string line;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream ss(line);ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};exists[q]=true;}
 ifstream ct(argv[2]);int q,code;while(ct>>q>>code){
  uint64_t known=uint64_t(code)<<27;int b=(code>>5)&1;
  ctx[q][b].push_back(known);
  ctx[q][b].push_back(known | (random64()&~(2047ULL<<27)));
 }
 vector<int>st;for(int q=0;q<1000;q++)if(exists[q])st.push_back(q);
 ofstream out(argv[3]);int found=0,mutations=0;
 for(int dq:st){if(dq==0||dq==84)continue;dropq=dq;
  for(int kq:st){if(kq==0||kq==dq)continue;keepq=kq;
   for(cb=0;cb<2;cb++){
    Tr a=tab[dq][1-cb],b=tab[kq][1-cb];
    if(a.w!=b.w||a.d!=b.d||project(a.z)!=project(b.z))continue;
    for(int helper:st){if(helper==dq)continue;
     for(int d:{-1,1})for(int w:{0,1}){
      rep={w,d,helper};mutations++;bool ok=true;
      for(int oq:{dq,kq}){for(uint64_t c:ctx[oq][cb]){if(!check(oq,c,31)){ok=false;break;}}if(!ok)break;}
      if(ok){out<<dq<<' '<<kq<<' '<<cb<<' '<<w<<' '<<d<<' '<<helper<<'\n';cout<<"FOUND "<<dq<<"->"<<kq<<" row "<<cb<<' '<<w<<' '<<d<<' '<<helper<<endl;found++;}
     }
    }
   }
  }
 }
 cout<<"DONE "<<found<<" / "<<mutations<<endl;
}
