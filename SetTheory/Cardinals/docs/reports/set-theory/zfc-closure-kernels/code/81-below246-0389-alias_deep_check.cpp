#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <string>
#include <cstdio>
using namespace std;
struct Row{int w,d,q;};array<array<Row,2>,256>T,base;
struct Case{bitset<512>a,z;int q,h;};vector<Case>cases;
struct Patch{Row entry;int target,rb;Row row;};
long long transitions=0,evaluations=0;
bool run(const Case&ex){
 auto tape=ex.a;int q=96,h=128,visits=0;evaluations++;
 for(int tick=0;tick<15000;tick++){
  transitions++;if(h<0||h>=512)return false;auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q;
  if(q==254)return ex.q==254;
  if(q==96){if(ex.q==96&&h==ex.h&&tape==ex.z)return true;if(++visits>15)return false;}
 }return false;
}
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;vector<int>states;
 while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(!b)states.push_back(q);}base=T;
 ifstream f(argv[2]);int n,k;while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>n;c.h+=128;
 for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++)f>>k;cases.push_back(c);}
 vector<Patch>patches;ifstream pf(argv[3]);string line;while(getline(pf,line)){
  Patch p;int ignore,maxsteps;
  if(sscanf(line.c_str(),"HIT entry=%d,%d,%d patch=%d,%d,%d,%d,%d maxsteps=%d",&p.entry.w,&p.entry.d,&p.entry.q,&p.target,&p.rb,&p.row.w,&p.row.d,&p.row.q,&maxsteps)==9)patches.push_back(p);
 }
 long long tried=0;int survivors=0;
 for(auto p:patches){
  T=base;T[218][0]=p.entry;T[p.target][p.rb]=p.row;
  int passed=0;for(auto &ex:cases){if(!run(ex))break;passed++;}tried++;
  cout<<(passed==(int)cases.size()?"PASS":"FAIL")<<" entry="<<p.entry.w<<","<<p.entry.d<<","<<p.entry.q<<" patch="<<p.target<<","<<p.rb<<","<<p.row.w<<","<<p.row.d<<","<<p.row.q<<" passed="<<passed<<endl;
  survivors+=passed==(int)cases.size();
  if(passed!=(int)cases.size())swap(cases[0],cases[passed]);
 }
 cout<<"DONE tried="<<tried<<" survivors="<<survivors<<" evaluations="<<evaluations<<" transitions="<<transitions<<endl;
}
