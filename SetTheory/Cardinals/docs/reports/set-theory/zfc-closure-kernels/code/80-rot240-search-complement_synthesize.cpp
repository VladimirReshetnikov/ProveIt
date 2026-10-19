#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <string>
#include <sstream>
#include <array>
#include <chrono>
using namespace std;
struct Act {int w,d,r;};
Act O[256][2]; vector<int> dom[256],states;bool exists_[256];
struct Case {int init,h,targetq,targeth,tape;};
int deleted_,retained_,offset_;
vector<Case> cases_[2];
long long tests_=0,attempts_=0;
bool check(Act first,int bit){
 for(const Case &c:cases_[bit]){
  int q=retained_,h=c.h,t=c.init;
  for(int step=0;step<25;step++){
   if(h<-3||h>3||q==254) return false;
   int b=(t>>(h+3))&1;
   Act a;
   if(step==0)a=first;
   else{
    if(q==retained_)return false;
    a=O[q][b];
    if(a.r==deleted_){a.w^=1;a.r=retained_;}
   }
   t=(t&~(1<<(h+3)))|(a.w<<(h+3));h+=a.d;q=a.r;
   if(q==c.targetq&&h==c.targeth&&t==c.tape)break;
   if(step==24)return false;
  }
 }
 return true;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);string line;while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream ss(line);int q,b,w,r;char d;ss>>q>>b>>w>>d>>r;O[q][b]={w,d=='R'?1:-1,r};exists_[q]=1;}
 for(int q=0;q<256;q++)if(exists_[q])states.push_back(q);
 ifstream g(argv[2]);int q,x;while(g>>q>>x)dom[q].push_back(x);
 auto begin=chrono::steady_clock::now();int survivors=0;
 for(int del:states){
  if(del==95)continue;
  set<int> directions;
  for(int q:states)for(int b=0;b<2;b++)if(q!=del&&O[q][b].r==del)directions.insert(O[q][b].d);
  if(directions.size()!=1)continue;
  deleted_=del;offset_=-*directions.begin();
  for(int ret:states){
   if(ret==del)continue;
   retained_=ret;cases_[0].clear();cases_[1].clear();
   for(int s:{del,ret})for(int x:dom[s]){
    Act a=O[s][(x>>3)&1];int h=0;
    int init=x^(s==del?(1<<(3+offset_)):0);
    int bit=(init>>3)&1;
    int targett=((x&~(1<<3))|(a.w<<3))^(a.r==del?(1<<(3+a.d+offset_)):0);
    cases_[bit].push_back({init,h,a.r==del?ret:a.r,a.d,targett});
   }
   attempts_++;vector<Act> good[2];
   for(int b=0;b<2;b++){
    if(b==1&&good[0].empty())break;
    for(int target:states)if(target!=del)for(int d:{-1,1})for(int w=0;w<2;w++){
     tests_++;Act a{w,d,target};if(check(a,b))good[b].push_back(a);
    }
   }
   if(!good[0].empty()&&!good[1].empty()){
    for(auto a:good[0])for(auto b:good[1]){
     cout<<del<<" "<<ret<<" "<<offset_<<" "<<a.w<<" "<<a.d<<" "<<a.r<<" "<<b.w<<" "<<b.d<<" "<<b.r<<"\n"<<flush;survivors++;
    }
   }
  }
 }
 cerr<<"attempts "<<attempts_<<" actions "<<tests_<<" survivors "<<survivors<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<"\n";
}
