#include <array>
#include <bitset>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <set>
using namespace std;
struct A{int w,d,z;};
array<array<A,2>,500>T;
struct Case{int index,pos,h;bitset<768>initial,expected;};
vector<Case> cases;
int run(Case const&c,int patch,A a,set<int>*visited=nullptr){
 bitset<768> tape=c.initial;int q=84,h=256;
 for(int k=0;k<2500;k++){
   if(k&&q==84&&h==256+c.h&&tape==c.expected)return k;
   if(q==254||h<0||h>=768||q==50)return -1;
   int b=tape[h],r=2*q+b;if(visited)visited->insert(r);
   A t=(r==patch)?a:T[q][b];
   if(t.d==0)return -1;tape[h]=t.w;h+=t.d;q=t.z;
 }return -1;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);string line;set<int>qs;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream s(line);s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};if(q!=50)qs.insert(q);}
 T[34][0]={0,-1,75};
 ifstream c(argv[2]);int n;c>>n;for(int k=0;k<n;k++){Case v;int na,nb,x;c>>v.index>>v.pos>>v.h>>na>>nb;for(int j=0;j<na;j++){c>>x;v.initial.set(x+256);}for(int j=0;j<nb;j++){c>>x;v.expected.set(x+256);}cases.push_back(v);}
 set<int> rows;run(cases[0],-1,{0,0,0},&rows);long trials=0,hits=0,screen=0;
 for(int row:rows){if(row/2==34)continue;for(int z:qs)for(int w:{0,1})for(int d:{-1,1}){A a{w,d,z};trials++;if(run(cases[0],row,a)<0)continue;screen++;bool pass=true;
  for(int k=1;k<(int)cases.size();k++)if(run(cases[k],row,a)<0){pass=false;break;}
  if(pass){hits++;cout<<"["<<row/2<<","<<row%2<<","<<w<<","<<d<<","<<z<<"]"<<endl;}
 }}
 cerr<<"rows "<<rows.size()<<" trials "<<trials<<" firstpass "<<screen<<" allpass "<<hits<<"\n";
}
