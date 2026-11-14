#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};
int main(int argc,char**argv){
 array<A,2> base[4000]; vector<int>qs;set<int>seen;ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n){if(q==301)continue;if(!seen.count(q)){seen.insert(q);qs.push_back(q);}base[q][b]={w,d=='R'?1:-1,n==301?88:n};}
 long long trials=0,success=0;
 for(int h:qs)if(h!=88)for(int hw=0;hw<2;hw++)for(int branch=0;branch<2;branch++)
 for(int wr=0;wr<2;wr++)for(int dr:{-1,1})for(int nr:qs){
  A change={wr,dr,nr};trials++;bool good=true;int dur[2]={};
  for(int prev=0;prev<2&&good;prev++){
   int x=-1,state=h,tape[2]={prev,hw};bool reached=false;
   for(int t=0;t<30;t++){
    if(x==1&&state==(prev?122:45)&&tape[0]==prev&&tape[1]==0){dur[prev]=t+1;reached=true;break;}
    if(x < -1||x>0)break;
    int bit=tape[x+1];A a;
    if(state==88&&bit==0)a={hw,-1,h};
    else if(state==h&&bit==branch)a=change;
    else if(seen.count(state))a=base[state][bit];else break;
    tape[x+1]=a.w;x+=a.d;state=a.n;
   }
   if(!reached)good=false;
  }
  if(good){success++;cout<<h<<' '<<hw<<' '<<branch<<' '<<wr<<' '<<dr<<' '<<nr<<' '<<dur[0]<<' '<<dur[1]<<'\n';}
 }
 cerr<<"trials "<<trials<<" solutions "<<success<<'\n';
}
