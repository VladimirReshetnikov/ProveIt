#include <array>
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cstdint>
using namespace std;
struct Row {int w,d,t;};
Row tab[256][2]; vector<int>states;
struct Test {uint64_t initial,wanted;int goalq,goalh,kind;};
bool test(Row r75,Row r131, int kind,int y,int& steps,int &append){
 const int off=4;uint64_t tape=1ull<<2;
 if(kind==0)for(int i=1;i<y+2;i++)tape|=1ull<<(i+off);
 uint64_t wanted=kind==0 ? (tape&~(1ull<<2))|(1ull<<3) : 0;
 int q=75,h=4;
 for(int i=0;i<400;i++){
  if(i&&q==(kind==0?112:48)&&h==(kind==0?1:2)){
   steps=i;
   if(kind==0)return tape==wanted;
   for(int k=0;k<16;k++) if(tape==((1ull<<2)|(((1ull<<(k+1))-1)<<4))){append=k;return true;}
   return false;
  }
  if(h<2||h>30||q==255||q==254)return false;
  bool b=(tape>>h)&1;
  Row r=q==75&&!b?r75 : q==131&&!b?r131 : tab[q][b];
  if(r.w)tape|=1ull<<h;else tape&=~(1ull<<h);
  h+=r.d;q=r.t;
 }
 return false;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);string s;getline(f,s);int q,b,w,t;char d;
 while(f>>q>>b>>w>>d>>t){tab[q][b]={w,d=='R'?1:-1,t};if(!b&&q!=255)states.push_back(q);}
 vector<Row>rows;for(int st:states)for(int ww:{0,1})for(int dd:{-1,1})rows.push_back({ww,dd,st});
 size_t nzero=0,ntail=0;
 for(auto a:rows)for(auto c:rows){
  int ns,append=0;
  if(!test(a,c,0,0,ns,append)||!test(a,c,0,1,ns,append)||!test(a,c,0,4,ns,append))continue;
  nzero++;
  if(!test(a,c,1,0,ns,append))continue;
  ntail++;
  cout<<"HIT 75/0 "<<a.w<<" "<<a.d<<" "<<a.t<<" 131/0 "<<c.w<<" "<<c.d<<" "<<c.t<<" tail "<<ns<<" append "<<append<<endl;
 }
 cerr<<"zero "<<nzero<<" tail "<<ntail<<endl;
}
