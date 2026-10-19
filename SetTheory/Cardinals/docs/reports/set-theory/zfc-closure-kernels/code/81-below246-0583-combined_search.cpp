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
vector<pair<int,int>> edges;
vector<vector<Row>> choices;
vector<int> testids;
long long checked=0;
int removed;
bool testall(){
 for(int ci:testids){
  auto &ex=tests[ci];auto tape=ex.a;int q=96,h=128,visits=0;bool pass=false;
  for(int tick=0;tick<4000;tick++){
   if(h<0||h>=512)break;
   auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q;
   if(q==254){pass=ex.q==254;break;}
   if(q==removed)break;
   if(q==96){if(ex.q==96&&h==ex.h&&tape==ex.z){pass=true;break;}if(++visits>15)break;}
  }
  if(!pass)return false;
 }
 return true;
}
void dfs(size_t j){
 if(j==edges.size()){
  checked++;
  if(testall()){
   cout<<"SURVIVOR delete "<<removed<<" ";
   for(auto [a,b]:edges){auto v=T[a][b];cout<<a<<' '<<b<<' '<<v.w<<' '<<v.d<<' '<<v.q<<" ; ";}
   cout<<endl;
  }
  return;
 }
 auto [a,b]=edges[j];auto orig=T[a][b];
 for(auto row:choices[j]){T[a][b]=row;dfs(j+1);}
 T[a][b]=orig;
}
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;
 while(tf>>q>>b>>w>>d>>t)T[q][b]={w,d=='R'?1:-1,t};
 ifstream f(argv[2]);int n,k;
 while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>n;c.h+=128;
 for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++){f>>k;c.used[k]=1;}tests.push_back(c);}
 ifstream opt(argv[3]);opt>>removed>>n;
 for(int j=0;j<n;j++){
  int a,b,m;opt>>a>>b>>m;edges.push_back({a,b});choices.push_back({});
  for(int i=0;i<m;i++){int w,d,q;opt>>w>>d>>q;choices.back().push_back({w,d,q});}
 }
 for(size_t i=0;i<tests.size();i++)if(tests[i].used[2*removed]||tests[i].used[2*removed+1])testids.push_back(i);
 mt19937 rng(246243);shuffle(testids.begin(),testids.end(),rng);
 dfs(0);cout<<"DONE removed="<<removed<<" combinations="<<checked<<endl;
}
