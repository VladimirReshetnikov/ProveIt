#include <array>
#include <fstream>
#include <iostream>
#include <vector>
#include <string>
#include <cstdint>
#include <algorithm>
#include <set>
using namespace std;
struct Row{int w,d,q;};array<array<Row,2>,256>T;
vector<uint32_t>seen;uint32_t epoch=0;int radius,width,ntapes;
bool test(Row entry,int mq,int mb,Row patch,int wanted,int&steps,vector<int>*trace=nullptr){
 int tape=wanted,q=218,h=radius;int previous=(wanted>>(radius-1))&1;
 if(++epoch==0){fill(seen.begin(),seen.end(),0);epoch=1;}
 for(int n=0;n<2000;n++){
  if(n&&h==radius+1&&q==(previous?105:23)){steps=n;return tape==wanted;}
  if(h<0||h>=width||q==254)return false;
  int key=(q*width+h)*ntapes+tape;if(seen[key]==epoch)return false;seen[key]=epoch;
  int b=(tape>>h)&1;
  if(trace)trace->push_back(2*q+b);
  Row r=q==218&&!b?entry:q==mq&&b==mb?patch:T[q][b];
  if(r.w)tape|=1<<h;else tape&=~(1<<h);q=r.q;h+=r.d;
 }return false;
}
int main(int argc,char**argv){
 radius=argc>2?stoi(argv[2]):2;width=2*radius+1;ntapes=1<<width;seen.resize(256*width*ntapes);
 ifstream f(argv[1]);string s;getline(f,s);int q,b,w,t;char d;vector<int>states;
 while(f>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(!b)states.push_back(q);}
 vector<int>cases={0,1<<(radius-1)};for(int tape=0;tape<ntapes;tape++)if(!(tape&(1<<radius))&&find(cases.begin(),cases.end(),tape)==cases.end())cases.push_back(tape);
 uint64_t recipes=0,hits=0,extended=0,temporary=0;
 for(int target:states)for(int w:{0,1})for(int d:{-1,1}){
  Row entry={w,d,target};int counterexample=-1,steps;
  for(int tape:cases)if(!test(entry,-1,0,{},tape,steps)){counterexample=tape;break;}
  if(counterexample<0){cout<<"DIRECT "<<w<<","<<d<<","<<target<<endl;continue;}
  vector<int>trace;test(entry,-1,0,{},counterexample,steps,&trace);sort(trace.begin(),trace.end());trace.erase(unique(trace.begin(),trace.end()),trace.end());
  for(int e:trace){
   int mq=e/2,mb=e%2;if(e==436)continue;
   for(int nw:{0,1})for(int nd:{-1,1})for(int nq:states){
    Row patch={nw,nd,nq};int steps=0,maxsteps=0;recipes++;bool good=true;
    for(int tape:cases){if(!test(entry,mq,mb,patch,tape,steps)){good=false;break;}maxsteps=max(maxsteps,steps);}
    if(!good)continue;hits++;extended+=maxsteps>3;temporary+=w;
    cout<<"HIT entry="<<w<<","<<d<<","<<target<<" patch="<<mq<<","<<mb<<","<<nw<<","<<nd<<","<<nq<<" maxsteps="<<maxsteps<<endl;
   }
  }
 }
 cerr<<"DONE radius="<<radius<<" recipes="<<recipes<<" hits="<<hits<<" extended="<<extended<<" temporary="<<temporary<<endl;
}
