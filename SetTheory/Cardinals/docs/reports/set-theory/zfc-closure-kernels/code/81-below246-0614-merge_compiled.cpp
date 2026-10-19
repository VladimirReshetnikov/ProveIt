#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
using namespace std;
struct Row {int w,d,q;};
array<array<Row,2>,4096> T;
struct Case {bitset<512> a,z;int q,h;bitset<4096> used;};
vector<Case> tests;
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;
 vector<int> states;
 while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(b==0)states.push_back(q);}
 ifstream f(argv[2]);int n,k;
 while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>n;c.h+=128;
 for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++){f>>k;c.used[k/2]=1;}tests.push_back(c);}
 array<vector<int>,4096> byq;
 for(size_t i=0;i<tests.size();i++)for(int v:states)if(tests[i].used[v])byq[v].push_back(i);
 mt19937 rng(250246);
 for(int v:states)shuffle(byq[v].begin(),byq[v].end(),rng);
 long long counter=0,steps=0;int survivors=0;
 for(int a:states){
  if(a==96)continue;
  int maxpass=0,best=-1;
  for(int c:states){if(a==c)continue; bool ok=true;int passed=0;
   for(int ci:byq[a]){
    auto &ex=tests[ci];auto tape=ex.a;int q=96,h=128,visits=0;
    bool pass=false;
    for(int tick=0;tick<4000;tick++){
     steps++;if(h<0||h>=512)break;
     auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q==a?c:row.q;
     if(q==254){pass=ex.q==254;break;}
     if(q==96){if(ex.q==96&&h==ex.h&&tape==ex.z){pass=true;break;}if(++visits>15)break;}
    }
    counter++;if(!pass){ok=false;break;}passed++;
   }
   if(passed>maxpass){maxpass=passed;best=c;}
   if(ok){cout<<"SURVIVOR "<<a<<" -> "<<c<<" cases "<<byq[a].size()<<endl;survivors++;}
  }
  cerr<<"state "<<a<<" best "<<best<<" cases "<<maxpass<<"/"<<byq[a].size()<<" total="<<counter<<" steps="<<steps<<endl;
 }
 cout<<"DONE survivors="<<survivors<<" tests="<<counter<<" steps="<<steps<<endl;
}
