#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
using namespace std;
struct Row {int w,d,q;};
array<array<Row,2>,256> T;
struct Case {bitset<512> a,z;int q,h;bitset<512> used;};
vector<Case> tests;
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;
 vector<int> states;
 while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(b==0)states.push_back(q);}
 ifstream f(argv[2]);int n,k;
 while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>n;c.h+=128;
 for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++){f>>k;c.used[k]=1;}tests.push_back(c);}
 array<vector<int>,512> bye;
 for(size_t i=0;i<tests.size();i++)for(int v:states)for(int b=0;b<2;b++)if(tests[i].used[2*v+b])bye[2*v+b].push_back(i);
 mt19937 rng(250246);
 for(auto &ids:bye)shuffle(ids.begin(),ids.end(),rng);
 long long counter=0,steps=0;int survivors=0;
 for(int a:{47,49,65})for(int b=1;b<2;b++){
  const auto orig=T[a][b];int e=2*a+b;
  if(orig.q==a||orig.q==96||orig.q==254)continue;
  int maxpass=0;
  for(int w=0;w<2;w++)for(int d:{-1,1})for(int c:states){
   bool ok=true;int passed=0;
   T[a][b]={w,d,c};
   for(int ci:bye[e]){
    auto &ex=tests[ci];auto tape=ex.a;int q=96,h=128,visits=0;
    bool pass=false;
    for(int tick=0;tick<4000;tick++){
     steps++;if(h<0||h>=512)break;
     auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q;
     if(q==254){pass=ex.q==254;break;}
     if(q==96){if(ex.q==96&&h==ex.h&&tape==ex.z){pass=true;break;}if(++visits>15)break;}
    }
    counter++;if(!pass){ok=false;break;}passed++;
   }
   if(passed>maxpass)maxpass=passed;
   if(ok){cout<<"SURVIVOR "<<a<<' '<<b<<" orig="<<orig.w<<' '<<orig.d<<' '<<orig.q<<" new="<<w<<' '<<d<<' '<<c<<" cases="<<bye[e].size()<<endl;survivors++;}
  }
  T[a][b]=orig;
  cerr<<"edge "<<a<<' '<<b<<" target "<<orig.q<<" maxpass "<<maxpass<<"/"<<bye[e].size()<<" total="<<counter<<" steps="<<steps<<endl;
 }
 cout<<"DONE survivors="<<survivors<<" tests="<<counter<<" steps="<<steps<<endl;
}
