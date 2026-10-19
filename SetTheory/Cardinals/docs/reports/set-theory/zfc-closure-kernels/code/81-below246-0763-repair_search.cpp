#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;
struct Row{int w,d,q;};array<array<Row,2>,256>T;
struct Case{bitset<512>a,z;int q,h;};vector<Case>cases;
bool run(const Case&ex){
 auto tape=ex.a;int q=96,h=128,visits=0;
 for(int tick=0;tick<20000;tick++){
  if(h<0||h>=512)return false;
  auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q;
  if(q==254)return ex.q==254;
  if(q==96){if(ex.q==96&&h==ex.h&&tape==ex.z)return true;if(++visits>15)return false;}
 }
 return false;
}
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;vector<int>states;
 while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(!b)states.push_back(q);}
 ifstream f(argv[2]);int n,k;
 while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>n;c.h+=128;
 for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++)f>>k;cases.push_back(c);}
 if(argc>8){int a=atoi(argv[5]),b=atoi(argv[6]),t=atoi(argv[7]),direction=atoi(argv[8]);T[a][b]={0,direction,t};}
 int a=atoi(argv[3]),b0=atoi(argv[4]);
 for(int w=0;w<2;w++)for(int d:{-1,1})for(int t:states){
  T[a][b0]={w,d,t};int passed=0;
  for(auto &ex:cases){if(!run(ex))break;passed++;}
  if(passed==int(cases.size()))cout<<"PASS "<<a<<' '<<b0<<' '<<w<<' '<<d<<' '<<t<<" passed="<<passed<<"/"<<cases.size()<<endl;
  else swap(cases[0],cases[passed]);
 }
}
