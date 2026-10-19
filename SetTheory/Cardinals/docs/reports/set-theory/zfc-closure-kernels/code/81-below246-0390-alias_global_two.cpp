#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <string>
#include <cstdint>
using namespace std;
struct Row{int w,d,q;};array<array<Row,2>,256>T,base;
struct Case{bitset<512>a,z;int q,h;};vector<Case>cases;
uint64_t transitions=0,evaluations=0;
bool run(const Case&ex){
 auto tape=ex.a;int q=96,h=128,visits=0;evaluations++;
 for(int tick=0;tick<5000;tick++){
  transitions++;if(h<0||h>=512)return false;auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q;
  if(q==254)return ex.q==254;
  if(q==96){if(ex.q==96&&h==ex.h&&tape==ex.z)return true;if(++visits>10)return false;}
 }return false;
}
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;vector<int>states;
 while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(!b)states.push_back(q);}base=T;
 ifstream f(argv[2]);int n,k;while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>n;c.h+=128;
 for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++)f>>k;cases.push_back(c);}
 uint64_t tried=0,hits=0;int maximum=0;
 for(int entrywrite:{1,0})for(int target:states)for(int entrydir:{-1,1})for(int rb:{0,1}){
  if(target==218&&rb==0)continue;
  T=base;T[218][0]={entrywrite,entrydir,target};int localmax=0;
  for(int w:{0,1})for(int d:{-1,1})for(int q:states){
   T[target][rb]={w,d,q};int passed=0;for(auto&ex:cases){if(!run(ex))break;passed++;}tried++;localmax=max(localmax,passed);
   if(passed==(int)cases.size()){
    hits++;cout<<"HIT entry="<<entrywrite<<","<<entrydir<<","<<target<<" patch="<<target<<","<<rb<<","<<w<<","<<d<<","<<q<<" cases="<<passed<<endl;
   }else swap(cases[0],cases[passed]);
  }
  if(localmax>maximum){maximum=localmax;cerr<<"progress tried="<<tried<<" maxpass="<<maximum<<" entry="<<entrywrite<<","<<entrydir<<","<<target<<" rb="<<rb<<endl;}
 }
 cout<<"DONE recipes="<<tried<<" survivors="<<hits<<" cases="<<evaluations<<" transitions="<<transitions<<" maxpass="<<maximum<<endl;
}
