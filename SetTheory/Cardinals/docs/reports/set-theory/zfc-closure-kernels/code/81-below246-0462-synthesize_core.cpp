#include <array>
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cstdint>
using namespace std;
struct Row{int w,d,t;};Row tab[256][2];vector<int>states;
bool test(Row a,Row b,Row one,int kind,int v,int&steps,int&app){
 const int off=4;uint64_t tape=1ull<<off;
 if(kind==0)for(int i=3;i<v+4;i++)tape|=1ull<<(i+off);
 if(kind==1)for(int i=2;i<v+2;i++)tape|=1ull<<(i+off);
 uint64_t wanted=kind==0?(tape&~(1ull<<off))|(1ull<<(off+1)):tape;
 int q=109,h=5;
 for(int i=0;i<1000;i++){
  if(i&&q==(kind==0?112:48)&&h==(kind==0?3:4)){
   steps=i;
   if(kind<2)return tape==wanted;
   for(int k=0;k<16;k++)if(tape==((1ull<<off)|(((1ull<<(k+1))-1)<<(off+2)))){app=k;return true;}
   return false;
  }
  if(h<4||h>30||q==255||q==254)return false;
  int read=(tape>>h)&1;
  Row r=q==75?(read?one:a):(q==109&&!read?b:tab[q][read]);
  if(r.w)tape|=1ull<<h;else tape&=~(1ull<<h);
  h+=r.d;q=r.t;
 }
 return false;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);string s;getline(f,s);int q,bit,w,t;char d;while(f>>q>>bit>>w>>d>>t){tab[q][bit]={w,d=='R'?1:-1,t};if(!bit&&q!=255)states.push_back(q);}
 vector<Row>rows;for(int st:states)for(int ww:{0,1})for(int dd:{-1,1})rows.push_back({ww,dd,st});
 size_t nzero=0,npos=0,ntail=0;
 for(Row one:vector<Row>{{1,-1,131},{1,1,131},{0,1,75},{1,-1,63}}){
  for(auto a:rows)for(auto b:rows){
   int ns,app;
   if(!test(a,b,one,0,0,ns,app)||!test(a,b,one,0,1,ns,app)||!test(a,b,one,0,4,ns,app))continue;nzero++;
   if(!test(a,b,one,1,1,ns,app)||!test(a,b,one,1,3,ns,app))continue;npos++;
   if(!test(a,b,one,2,0,ns,app))continue;ntail++;
   cout<<"HIT 75/0 "<<a.w<<" "<<a.d<<" "<<a.t<<" 109/0 "<<b.w<<" "<<b.d<<" "<<b.t<<" 75/1 "<<one.w<<" "<<one.d<<" "<<one.t<<" tail "<<ns<<" append "<<app<<endl;
  }
 }
 cerr<<"zero "<<nzero<<" positive "<<npos<<" tail "<<ntail<<endl;
}
