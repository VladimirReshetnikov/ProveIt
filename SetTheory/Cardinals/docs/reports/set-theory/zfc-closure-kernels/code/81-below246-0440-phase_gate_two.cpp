#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <string>
#include <cstdint>
using namespace std;
struct Row { int w,d,q; };
array<array<Row,2>,256> T,base;
struct Case { bitset<512> a,z,used; int q,h; bool before; };
vector<Case> cases;
uint64_t transitions=0,evaluations=0;
bool run(const Case& ex) {
 auto tape=ex.a; int q=96,h=128,visits=0; evaluations++;
 for(int tick=0;tick<5000;tick++) {
  transitions++; if(h<0||h>=512)return false;
  auto row=T[q][tape[h]]; tape[h]=row.w; h+=row.d; q=row.q;
  if(q==254)return ex.q==254;
  if(q==96) {
   if(ex.q==96&&h==ex.h&&tape==ex.z)return true;
   if(++visits>15)return false;
  }
 }
 return false;
}
int main(int argc,char**argv) {
 ifstream tf(argv[1]); string s; getline(tf,s); int q,b,w,t; char d;
 vector<int> states;
 while(tf>>q>>b>>w>>d>>t) { T[q][b]={w,d=='R'?1:-1,t}; if(!b)states.push_back(q); }
 base=T; ifstream f(argv[2]); int n,k;
 while(f>>n) {
  Case c; for(int i=0;i<n;i++) { f>>k; c.a[k+128]=1; }
  f>>c.q>>c.h>>n; c.h+=128;
  for(int i=0;i<n;i++) { f>>k; c.z[k+128]=1; }
  f>>n; for(int i=0;i<n;i++) { f>>k; c.used[k]=1; }
  c.before=run(c); cases.push_back(c);
 }
 uint64_t tried=0,hits=0;
 for(int gate:{47,49,65}) {
  vector<int> ids;
  for(int i=0;i<(int)cases.size();i++)
   if(cases[i].before||cases[i].used[2*gate+1])ids.push_back(i);
  int maximum=0;
  // Retain the first phase1 and move to a borrowed existing state.
  // Change one row of that state to implement its phase discriminator.
  for(int target:states)for(int dir:{1,-1})for(int rb:{0,1}) {
   if(target==gate&&rb==1)continue;
   T=base; T[gate][1]={1,dir,target};
   for(int wr:{0,1})for(int dr:{-1,1})for(int qr:states) {
    T[target][rb]={wr,dr,qr}; int passed=0;
    for(int i:ids) { if(!run(cases[i]))break; passed++; }
    tried++; maximum=max(maximum,passed);
    if(passed==(int)ids.size()) {
     hits++; cout<<"HIT gate="<<gate<<" entry=1,"<<dir<<","<<target
       <<" patch="<<target<<","<<rb<<","<<wr<<","<<dr<<","<<qr
       <<" cases="<<passed<<endl;
    } else swap(ids[0],ids[passed]);
   }
  }
  cerr<<"gate="<<gate<<" recipes="<<tried<<" maxpass="<<maximum<<"/"<<ids.size()
      <<" evaluations="<<evaluations<<" transitions="<<transitions<<endl;
 }
 cout<<"DONE recipes="<<tried<<" survivors="<<hits<<" cases="<<evaluations
     <<" transitions="<<transitions<<endl;
}
