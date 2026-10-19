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
struct Case {bitset<512> a,z,mask;int q,h,end;bitset<512> used;};
vector<Case> tests;
bool matches(const bitset<512>&tape,const Case &ex){
 if(((tape^ex.z)&ex.mask).any())return false;
 int last=511;while(last>=ex.end&&!tape[last])last--;
 if(last<=ex.end||tape[ex.end])return false;
 for(int i=ex.end;i<last;i++)if(!tape[i]&&!tape[i+1])return false;
 return true;
}
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;
 bool merge=argc>3&&string(argv[3])=="merge";
 vector<int> states;
 while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(b==0)states.push_back(q);}
 ifstream f(argv[2]);int n,k;
 while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>c.end>>n;c.h+=128;c.end+=128;
 for(int i=0;i<c.end;i++)c.mask[i]=1;
 for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++){f>>k;c.used[k]=1;}tests.push_back(c);}
 array<vector<int>,512> bye;
 for(size_t i=0;i<tests.size();i++)for(int v:states)for(int b=0;b<(merge?1:2);b++)
  if(merge?(tests[i].used[2*v]||tests[i].used[2*v+1]):tests[i].used[2*v+b])bye[2*v+b].push_back(i);
 mt19937 rng(250246);for(auto &ids:bye)shuffle(ids.begin(),ids.end(),rng);
 long long counter=0,steps=0;int survivors=0;
 for(int a:states)for(int b=0;b<(merge?1:2);b++){
  const auto orig=T[a][b];int e=2*a+b;
  if(merge?a==96:(orig.q==a||orig.q==96||orig.q==254))continue;
  for(int w=0;w<(merge?1:2);w++)for(int d:(merge?vector<int>{1}:vector<int>{-1,1}))for(int c:states){
   if(c==(merge?a:orig.q))continue;bool ok=true;int passed=0;
   if(!merge)T[a][b]={w,d,c};
   for(int ci:bye[e]){
    auto &ex=tests[ci];auto tape=ex.a;int q=96,h=128,visits=0;bool pass=false;
    for(int tick=0;tick<4000;tick++){
     steps++;if(h<0||h>=512)break;
     auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=(merge&&row.q==a)?c:row.q;
     if(q==254){pass=ex.q==254;break;}
     if(q==96){if(ex.q==96&&h==ex.h&&matches(tape,ex)){pass=true;break;}if(++visits>15)break;}
    }
    counter++;if(!pass){ok=false;break;}passed++;
   }
   if(ok){cout<<"SURVIVOR "<<a<<' '<<b<<" orig="<<orig.w<<' '<<orig.d<<' '<<orig.q<<" new="<<w<<' '<<d<<' '<<c<<" cases="<<bye[e].size()<<endl;survivors++;}
  }
  T[a][b]=orig;
 }
 cout<<"DONE survivors="<<survivors<<" tests="<<counter<<" steps="<<steps<<endl;
}
