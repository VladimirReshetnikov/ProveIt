#include <array>
#include <fstream>
#include <iostream>
#include <vector>
#include <string>
#include <cstdint>
using namespace std;
struct Row {int w,d,q;};array<array<Row,2>,256>T;
int stamp[256*3*8],epoch=0;
bool test(Row entry,int target,int rb,Row patch,int previous,int next,int &steps){
 const int wanted=(previous?1:0)|(next?4:0);int tape=wanted,q=218,h=1;
 ++epoch;
 for(int n=0;n<1000;n++){
  if(n&&h==2&&q==(previous?105:23)){steps=n;return tape==wanted;}
  if(h<0||h>2||q==254)return false;
  const int key=(q*3+h)*8+tape;
  if(stamp[key]==epoch)return false;stamp[key]=epoch;
  const int b=(tape>>h)&1;
  Row r=q==218&&b==0?entry:(q==target&&b==rb?patch:T[q][b]);
  if(r.w)tape|=1<<h;else tape&=~(1<<h);
  q=r.q;h+=r.d;
 }
 return false;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);string s;getline(f,s);int q,b,w,t;char d;vector<int>states;
 while(f>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(!b)states.push_back(q);}
 uint64_t recipes=0,hits=0;
 for(int target:states)for(int w:{0,1})for(int d:{-1,1})for(int rb:{0,1}){
  if(target==218&&rb==0)continue;
  Row entry={w,d,target};
  for(int nw:{0,1})for(int nd:{-1,1})for(int nq:states){
   Row patch={nw,nd,nq};int steps=0;recipes++;
   if(!test(entry,target,rb,patch,0,0,steps)||!test(entry,target,rb,patch,1,0,steps)||!test(entry,target,rb,patch,0,1,steps)||!test(entry,target,rb,patch,1,1,steps))continue;
   hits++;cout<<"HIT entry="<<w<<","<<d<<","<<target<<" patch="<<target<<","<<rb<<","<<nw<<","<<nd<<","<<nq<<" steps="<<steps<<endl;
  }
 }
 cerr<<"DONE recipes="<<recipes<<" hits="<<hits<<endl;
}
