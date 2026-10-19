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
struct Case {bitset<512> a,z;int q,h;string pc;array<int,9> regs;bitset<512> used;};
vector<Case> tests;
bool matches(const bitset<512>&tape,const Case &ex,int h){
 if(h<1||h+40>=512||!tape[h-1])return false;
 for(int i=0;i<h-1;i++)if(tape[i])return false;
 for(int i=0;i<(int)ex.pc.size();i++)if(h+i>=512||tape[h+i]!=(ex.pc[i]=='1'))return false;
 int header=h+ex.pc.size();while(header<512&&!tape[header])header++;
 if(header==512||header-h<40)return false;
 int at=header+1;
 for(int r:ex.regs){
  if(at>=512||tape[at])return false;
  for(int j=1;j<=r+1;j++)if(at+j>=512||!tape[at+j])return false;
  at+=r+2;
 }
 int last=511;while(last>=at&&!tape[last])last--;
 if(last<=at||tape[at])return false;
 for(int i=at;i<last;i++)if(!tape[i]&&!tape[i+1])return false;
 return true;
}
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;
 bool merge=argc>3&&string(argv[3])=="merge";
 vector<int> states;
 while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(b==0)states.push_back(q);}
 ifstream f(argv[2]);int n,k;
 while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>c.pc;c.h+=128;
 if(c.pc=="-")c.pc="";for(int &r:c.regs)f>>r;f>>n;
 for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++){f>>k;c.used[k]=1;}tests.push_back(c);}
 for(Case &ex:tests) {
  ex.used.reset();auto tape=ex.a;int state=96,h=128,visits=0;bool pass=false;
  for(int tick=0;tick<30000;tick++) {
   if(h<0||h>=512)break;
   int read=tape[h];ex.used[2*state+read]=1;
   auto row=T[state][read];tape[h]=row.w;h+=row.d;state=row.q;
   if(state==254){pass=ex.q==254;break;}
   if(state==96){if(ex.q==96&&matches(tape,ex,h)){pass=true;break;}if(++visits>40)break;}
  }
  if(!pass){cerr<<"NEUTRAL REWRITE FAILED"<<endl;return 3;}
 }
 array<int,256> indegree{};
 for(int a:states)for(int b=0;b<2;b++)if(T[a][b].q!=a)indegree[T[a][b].q]++;
 cerr<<"NEUTRAL REWRITE PASSED "<<tests.size()<<" tests"<<endl;
 array<vector<int>,512> bye;
 for(size_t i=0;i<tests.size();i++)for(int v:states)for(int b=0;b<(merge?1:2);b++)
  if(merge?(tests[i].used[2*v]||tests[i].used[2*v+1]):tests[i].used[2*v+b])bye[2*v+b].push_back(i);
 mt19937 rng(250246);for(auto &ids:bye)shuffle(ids.begin(),ids.end(),rng);
 long long counter=0,steps=0;int survivors=0;
 for(int a:states)for(int b=0;b<(merge?1:2);b++){
  const auto orig=T[a][b];int e=2*a+b;
  if(merge?a==96:(orig.q==a||orig.q==96||orig.q==254))continue;
  if(!merge&&indegree[orig.q]!=1&&orig.q!=48&&orig.q!=2&&orig.q!=69)continue;
  for(int w=0;w<(merge?1:2);w++)for(int d:(merge?vector<int>{1}:vector<int>{-1,1}))for(int c:states){
   if(c==(merge?a:orig.q))continue;bool ok=true;int passed=0;
   if(!merge)T[a][b]={w,d,c};
   for(int ci:bye[e]){
    auto &ex=tests[ci];auto tape=ex.a;int q=96,h=128,visits=0;bool pass=false;
    for(int tick=0;tick<4000;tick++){
     steps++;if(h<0||h>=512)break;
     auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=(merge&&row.q==a)?c:row.q;
     if(q==254){pass=ex.q==254;break;}
     if(q==96){if(ex.q==96&&matches(tape,ex,h)){pass=true;break;}if(++visits>15)break;}
    }
    counter++;if(!pass){ok=false;break;}passed++;
   }
   if(ok){cout<<"SURVIVOR "<<a<<' '<<b<<" orig="<<orig.w<<' '<<orig.d<<' '<<orig.q<<" new="<<w<<' '<<d<<' '<<c<<" cases="<<bye[e].size()<<endl;survivors++;}
  }
  T[a][b]=orig;
 }
 cout<<"DONE survivors="<<survivors<<" tests="<<counter<<" steps="<<steps<<endl;
}
