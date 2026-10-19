#include <vector>
#include <array>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
using namespace std;
struct Row { int w=0,d=1,t=254; };
int main(int argc,char**argv){
 for(int z=1;z<argc;z++){
  string f=argv[z],line; ifstream in(f);array<array<Row,2>,300>T{};
  while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream is(line);int q,b,w,t;char d;if(is>>q>>b>>w>>d>>t)T[q][b]={w,d=='R'?1:-1,t};}
  int q=95,h=1000000,mn=4000000,mx=-1;long long N=5000000;vector<unsigned char>tp(3000000);vector<int> vals;bool ok=false;
  for(long long i=0;i<=N;i++){
   if(q==254){cout<<f<<" HALT "<<i<<"\n";ok=true;break;}
   if(q==96&&tp[h-1]&&mn==h-1){
    int j=h;while(j<=mx&&!tp[j])j++;int gap=j-h;
    if(gap>=64&&j<=mx){
     vals.clear();int p=j+1;bool valid=true;
     while(p<=mx){if(tp[p]||!tp[p+1]){valid=false;break;}p++;int start=p;while(p<=mx&&tp[p])p++;vals.push_back(p-start-1);}
     if(valid&&p==mx+1&&vals.size()>=10){cout<<f<<" FRAME "<<i<<" "<<h-1000000<<" "<<gap<<" "<<vals.size();for(int j=0;j<9;j++)cout<<" "<<vals[j];cout<<"\n";ok=true;break;}
    }
   }
   Row a=T[q][tp[h]];
   tp[h]=a.w;
   if(a.w){mn=min(mn,h);mx=max(mx,h);}else{if(h==mn){while(mn<=mx&&!tp[mn])mn++;}if(h==mx){while(mx>=mn&&!tp[mx])mx--;}}
   q=a.t;h+=a.d;
   if(h<1||h+1>=tp.size()){cout<<f<<" TAPE_BOUND "<<i<<"\n";ok=true;break;}
  }
  if(!ok)cout<<f<<" FUEL "<<N<<"\n";
 }
}
