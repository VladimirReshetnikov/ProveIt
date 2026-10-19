#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <string>
#include <sstream>
#include <array>
#include <chrono>
#include <deque>
#include <algorithm>
using namespace std;
struct Act {int w,d,r;};
struct Conf {int q,h,t;};
Act O[256][2],N[256][2];vector<int> states,dom[256];bool present[256];int radius_,width_,mask_,limit_=32;
int del_,ret_;
bool check(int s,int x){
 Conf old[64];int count=0;
 int q=s,h=0,t=x;
 for(int a=1;a<=limit_;a++){
  if(q==254||h < -radius_ ||h>radius_)break;
  int b=(t>>(h+radius_))&1;Act z=O[q][b];
  t=(t&~(1<<(h+radius_)))|(z.w<<(h+radius_));q=z.r;h+=z.d;
  old[count++]={q==del_?ret_:q,h,t};
 }
 q=s==del_?ret_:s;h=0;t=x;
 for(int a=1;a<=limit_;a++){
  if(q==254||h < -radius_ ||h>radius_)return false;
  int b=(t>>(h+radius_))&1;Act z=N[q][b];
  t=(t&~(1<<(h+radius_)))|(z.w<<(h+radius_));q=z.r;h+=z.d;
  for(int j=0;j<count;j++)if(q==old[j].q&&h==old[j].h&&t==old[j].t)return true;
 }
 return false;
}
int main(int argc,char**argv){
 radius_=argc>2?atoi(argv[2]):4;width_=2*radius_+1;mask_=(1<<width_)-1;
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream ss(line);int q,b,w,r;char d;ss>>q>>b>>w>>d>>r;O[q][b]={w,d=='R'?1:-1,r};present[q]=1;}
 for(int q=0;q<256;q++)if(present[q])states.push_back(q);
 vector<vector<bool>> seen(256,vector<bool>(1<<width_));deque<pair<int,int>> todo;
 for(int x=0;x<=mask_;x++){seen[95][x]=1;todo.emplace_back(95,x);}
 while(!todo.empty()){
  auto [q,x]=todo.front();todo.pop_front();if(q==254)continue;
  Act a=O[q][(x>>radius_)&1];int y=(x&~(1<<radius_))|(a.w<<radius_);
  int z=a.d==1?y>>1:(y<<1)&mask_;int e=a.d==1?1<<(width_-1):1;
  for(int v:{z,z|e})if(!seen[a.r][v]){seen[a.r][v]=1;todo.emplace_back(a.r,v);}
 }
 for(int q:states)for(int x=0;x<=mask_;x++)if(seen[q][x])dom[q].push_back(x);
 auto start=chrono::steady_clock::now();long long attempts=0;int survivors=0;
 for(int i=0;i<int(states.size());i++)for(int j=i+1;j<int(states.size());j++){
  del_=states[j];ret_=states[i];if(del_==95)swap(del_,ret_);
  for(int overlay=0;overlay<4;overlay++){
   attempts++;
   for(int q:states)for(int b=0;b<2;b++){N[q][b]=O[q][b];if(N[q][b].r==del_)N[q][b].r=ret_;}
   for(int b=0;b<2;b++)if((overlay>>b)&1){N[ret_][b]=O[del_][b];if(N[ret_][b].r==del_)N[ret_][b].r=ret_;}
   bool ok=true;
   for(int q:{del_,ret_}){for(int x:dom[q])if(!check(q,x)){ok=false;break;}if(!ok)break;}
   if(ok){cout<<del_<<" "<<ret_<<" "<<overlay<<"\n"<<flush;survivors++;}
  }
 }
 cerr<<"radius "<<radius_<<" max_steps "<<limit_<<" attempts "<<attempts<<" survivors "<<survivors<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
