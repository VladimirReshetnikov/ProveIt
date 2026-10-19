#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
using namespace std;
struct Row {int w,d,q;};array<array<Row,2>,256>T;
struct Case{bitset<512>a,z,mask,used;int q,h,spare;};vector<Case>tests;
bool matches(const Case&ex,const bitset<512>&tape){
 if((tape&ex.mask)!=(ex.z&ex.mask))return false;
 int p=ex.spare,blocks=0;
 while(p<510&&!tape[p]&&tape[p+1]){blocks++;p++;while(p<512&&tape[p])p++;}
 if(!blocks)return false;
 for(int i=p;i<512;i++)if(tape[i])return false;
 return true;
}
int main(int argc,char**argv){
 ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;
 vector<int>states;while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(!b)states.push_back(q);}
 ifstream cf(argv[2]);int n,k;while(cf>>n){Case c;for(int i=0;i<n;i++){cf>>k;c.a[k+128]=1;}cf>>c.q>>c.h>>n;c.h+=128;
 for(int i=0;i<n;i++){cf>>k;c.z[k+128]=1;}cf>>n;for(int i=0;i<n;i++){cf>>k;c.used[k]=1;}
 c.spare=c.z[168]?169:170;
 if(c.q==96)for(int i=0;i<9;i++){if(c.z[c.spare]||!c.z[c.spare+1]){cerr<<"bad shape";return 2;}c.spare++;while(c.z[c.spare])c.spare++;}
 for(int i=0;i<c.spare;i++)c.mask[i]=1;tests.push_back(c);}
 mt19937 rng(424981);shuffle(tests.begin(),tests.end(),rng);
 int removed=argc>3?stoi(argv[3]):-1;
 for(int a:states)for(int b=0;b<2;b++){
  if(removed>=0&&T[a][b].q!=removed)continue;
  if(removed<0&&(a<73||a>255|| (a>83&&a!=95&&a!=109&&a!=112&&a!=131&&a!=255)))continue;
  auto orig=T[a][b];int hits=0,maxpass=0;
  for(int w=0;w<2;w++)for(int d:{-1,1})for(int c:states){
   if(c==orig.q||c==removed)continue;T[a][b]={w,d,c};int passed=0;
   for(auto&ex:tests){if(!ex.used[2*a+b])continue;
    auto tape=ex.a;int q=96,h=128,visits=0;bool ok=false;
    for(int tick=0;tick<30000;tick++){
     if(h<0||h>=512||q==removed)break;
     auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q;
     if(q==254){ok=ex.q==254;break;}
     if(q==96){if(ex.q==96&&h==ex.h&&matches(ex,tape)){ok=true;break;}if(++visits>15)break;}
    }
    if(!ok)break;passed++;
   }
   maxpass=max(maxpass,passed);
   int required=0;for(auto&ex:tests)required+=ex.used[2*a+b];
   if(passed==required){hits++;cout<<"HIT "<<a<<" "<<b<<" new="<<w<<","<<d<<","<<c<<" cases="<<passed<<endl;}
  }
  T[a][b]=orig;cerr<<"edge "<<a<<" "<<b<<" hits="<<hits<<" maxpass="<<maxpass<<endl;
 }
}
