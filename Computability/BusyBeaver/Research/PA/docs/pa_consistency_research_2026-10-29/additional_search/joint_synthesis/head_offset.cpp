// Candidate screen only: observed local windows are not reachability proofs.
#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <iostream>
#include <cstdint>
using namespace std;
struct Tr{int w,d,z;};Tr tab[1000][2];bool exists[1000];vector<uint64_t> ctx[1000];
uint64_t rng=5417389024ULL;uint64_t random64(){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
int dropq,keepq,offset;
int project(int q){return q==dropq?keepq:q;}
bool check(uint64_t before,int lim){
 const int c=32;int b=(before>>c)&1;Tr old=tab[dropq][b];int es=project(old.z),eh=c+old.d+(old.z==dropq?offset:0);
 uint64_t expected=(before&~(1ULL<<c))|(uint64_t(old.w)<<c);
 int s=keepq,h=c+offset;uint64_t tape=before;
 for(int i=0;i<lim;i++){
  if(s==254||h<1||h>62)return false;
  int bit=(tape>>h)&1;Tr t=tab[s][bit];
  if(t.z==dropq){t.z=keepq;t.d=-t.d;}
  tape=(tape&~(1ULL<<h))|(uint64_t(t.w)<<h);h+=t.d;s=t.z;
  if(s==es&&h==eh&&tape==expected)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc<4)return 1;ifstream in(argv[1]);string ln;
 while(getline(in,ln)){if(ln.empty()||ln[0]=='#')continue;int q,b,w,z;char d;istringstream ss(ln);ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};exists[q]=true;}
 ifstream ct(argv[2]);int q,code;while(ct>>q>>code){uint64_t known=uint64_t(code)<<27;ctx[q].push_back(known);ctx[q].push_back(known|(random64()&~(2047ULL<<27)));}
 vector<int> st;for(int q=0;q<1000;q++)if(exists[q])st.push_back(q);
 ofstream out(argv[3]);long tested=0;int found=0;
 for(int dq:st){if(dq==0)continue;int dir=0;bool conflict=false;for(int q:st)for(int b=0;b<2;b++)if(tab[q][b].z==dq){if(dir&&dir!=tab[q][b].d)conflict=true;dir=tab[q][b].d;}
  if(conflict||!dir)continue;dropq=dq;offset=-2*dir;
  for(int kq:st){if(kq==dq)continue;keepq=kq;tested++;bool pass=true;
   for(uint64_t c:ctx[dq])if(!check(c,63)){pass=false;break;}
   if(pass){found++;out<<dq<<' '<<kq<<' '<<offset<<'\n';cout<<"FOUND "<<dq<<"->"<<kq<<" offset "<<offset<<endl;}
  }
 }
 cout<<"DONE tested "<<tested<<" found "<<found<<endl;
}
