#include <array>
#include <vector>
#include <tuple>
#include <iostream>
#include <fstream>
#include <random>
using namespace std;
struct A{int w,d,q;bool operator==(const A&o)const{return w==o.w&&d==o.d&&q==o.q;}};
struct P{int s,t,b;};
const int N=196,H=197,W=257,O=128;
array<array<A,2>,198> orig,tab;
vector<P> ps;
array<int,198> tag,proj;
array<array<unsigned char,W>,8> tapes;
long long tested=0;
bool testone(int old,int b,int mode,int limit){
 auto tape=tapes[mode];tape[O-1]=tag[old];tape[O]=b;
 auto initial=tape;
 int q=proj[old],h=O;
 A ex=orig[old][b];int eq=proj[ex.q],eh=O+ex.d;
 initial[O]=ex.w;
 for(int i=0;i<limit;i++){
  if(q==N||h<0||h>=W)return false;
  A a=tab[q][tape[h]];tape[h]=a.w;h+=a.d;q=a.q;
  if(q==eq&&h==eh&&tape==initial)return true;
 }
 return false;
}
bool pairtest(P p,int mode,int limit){return testone(p.s,p.b,mode,limit)&&testone(p.t,p.b,mode,limit);}
int main(int argc,char**argv){
 ifstream f(argv[1]);int s,b,w,q;char d;
 while(f>>s>>b>>w>>d>>q)orig[s][b]={w,d=='R'?1:-1,q};
 for(int i=0;i<198;i++){tag[i]=-1;proj[i]=i;}
 for(int j=1;j<N;j++){
  int found=-1;bool ok=true;
  for(int i=0;i<N;i++)for(int k=0;k<2;k++)if(orig[i][k].q==j){
   auto a=orig[i][k];if(a.d!=1)ok=false;
   if(found<0)found=a.w;else if(found!=a.w)ok=false;
  } if(ok)tag[j]=found;
 }
 for(int s=1;s<N;s++)for(int t=s+1;t<N;t++)if(tag[s]>=0&&tag[t]>=0&&tag[s]!=tag[t])
  for(int b=0;b<2;b++)if(orig[s][1-b]==orig[t][1-b]&&!(orig[s][b]==orig[t][b])&&orig[s][b].w==b&&orig[s][b].d==1&&orig[t][b].w==b&&orig[t][b].d==1)ps.push_back({s,t,b});
 cerr<<"Pairs "<<ps.size()<<endl;
 mt19937 gen(17);
 for(int m=0;m<8;m++)for(int k=0;k<W;k++)tapes[m][k]=m==0?0:m==1?1:m==2?k%2:m==3?1-k%2:gen()%2;
 int limit=argc>2?atoi(argv[2]):35;
 vector<tuple<P,P,A,A>> survivors;
 for(int i=0;i<(int)ps.size();i++)for(int j=i+1;j<(int)ps.size();j++){
  auto a=ps[i],c=ps[j];if(a.s==c.s||a.s==c.t||a.t==c.s||a.t==c.t)continue;
  for(int k=0;k<198;k++)proj[k]=k;
  proj[a.t]=a.s;proj[c.t]=c.s;
  tab=orig;
  for(int k=0;k<N;k++)for(int b=0;b<2;b++)tab[k][b].q=proj[tab[k][b].q];
  tab[a.s][a.b]={a.b,-1,H};tab[c.s][c.b]={c.b,-1,H};
  for(int d0:{1,-1})for(int q0=0;q0<=H;q0++)if(q0!=N&&proj[q0]==q0)
  for(int d1:{1,-1})for(int q1=0;q1<=H;q1++)if(q1!=N&&proj[q1]==q1){
   ++tested;tab[H][0]={0,d0,q0};tab[H][1]={1,d1,q1};
   if(!pairtest(a,0,limit)||!pairtest(c,0,limit))continue;
   bool ok=true;for(int m=1;m<8&&ok;m++)ok=pairtest(a,m,limit)&&pairtest(c,m,limit);
   if(ok){survivors.emplace_back(a,c,tab[H][0],tab[H][1]);
    cout<<a.s<<" "<<a.t<<" "<<a.b<<" ; "<<c.s<<" "<<c.t<<" "<<c.b<<" ; "<<d0<<" "<<q0<<" ; "<<d1<<" "<<q1<<endl;
   }
  }
 }
 cerr<<"Tested "<<tested<<" survivors "<<survivors.size()<<endl;
}
