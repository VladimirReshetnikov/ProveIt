#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <chrono>
using namespace std;
struct Row{int w,d,z;};
struct Test{int site,pos,halt,steps;array<uint64_t,4> start,goal,used;};
Row base[196][2],tab[196][2];
vector<Test> tests;
long long checked=0,execs=0;
bool run(const Test &x,int root){
 array<uint64_t,4> t=x.start;int q=root,h=32;
 int diff=0;for(int j=0;j<4;j++)diff+=__builtin_popcountll(t[j]^x.goal[j]);
 int budget=max(800,2*x.steps+64);++execs;
 for(int k=0;k<budget;k++){
  if(k && ((x.halt && q==196)||(!x.halt && q==root && h==32 && !diff)))return true;
  if(q==196 || h<0 || h>=256)return false;
  int word=h>>6;uint64_t mask=1ULL<<(h&63);int b=bool(t[word]&mask);
  Row r=tab[q][b];
  if(b!=r.w){diff+=(bool(x.goal[word]&mask)==bool(b)?1:-1);t[word]^=mask;}
  q=r.z;h+=r.d;
 }
 return false;
}
int main(int argc,char**argv){
 ifstream tf(argv[1]);int q,b,w,z;char d;
 while(tf>>q>>b>>w>>d>>z)base[q][b]={w,d=='R'?1:-1,z};
 ifstream in(argv[2]);int n;in>>n;
 for(int i=0;i<n;i++){Test x;in>>x.site>>x.pos>>x.halt>>x.steps;for(auto &u:x.start)in>>u;for(auto &u:x.goal)in>>u;for(auto &u:x.used)in>>u;tests.push_back(x);}
 if(!in){cerr<<"bad tests\n";return 2;}
 for(int q=0;q<196;q++)for(int b=0;b<2;b++)tab[q][b]=base[q][b];
 for(auto &x:tests)if(!run(x,75)){cerr<<"baseline fail "<<x.site<<","<<x.pos<<"\n";return 3;}
 ifstream df(argv[3]);vector<int> drops;while(df>>q)drops.push_back(q);
 vector<int> list;
 for(int a:drops){
  long long survived=0;auto start=chrono::steady_clock::now();
  for(int b=0;b<196;b++)if(b!=a){
   for(int q=0;q<196;q++)for(int r=0;r<2;r++){tab[q][r]=base[q][r];if(tab[q][r].z==a)tab[q][r].z=b;}
   list.clear();for(int j=0;j<n;j++)if((tests[j].used[a>>6]>>(a&63)&1)||(tests[j].used[b>>6]>>(b&63)&1))list.push_back(j);
   int root=a==75?b:75;
   for(int r=0;r<2;r++){
    Row save=tab[b][r];
    for(int write=0;write<2;write++)for(int dir:{-1,1})for(int to=0;to<=196;to++)if(to!=a){
     tab[b][r]={write,dir,to};++checked;
     bool pass=true;
     for(int j:list)if(!run(tests[j],root)){pass=false;break;}
     if(pass){++survived;cout<<"SURVIVOR "<<a<<" "<<b<<" "<<r<<" "<<write<<" "<<dir<<" "<<to<<endl;}
    }
    tab[b][r]=save;
   }
  }
  double sec=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  cerr<<"drop "<<a<<" total "<<checked<<" runs "<<execs<<" survivors "<<survived<<" seconds "<<sec<<endl;
 }
}
