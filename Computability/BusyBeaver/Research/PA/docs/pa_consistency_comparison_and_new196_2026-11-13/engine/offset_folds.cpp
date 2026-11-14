// Offset quotients: one removed state is represented two cells behind its old
// head after uniformly directed incoming transitions. Every redirect flips
// its direction. Exact finite stuttering obligations are checked on 9 cells.
#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <string>
using namespace std;
constexpr int N=196,R=4,S=64;
struct Row{int w,d,t;}; Row tab[N][2]; vector<int> contexts[N];
int main(int argc,char**argv){
 if(argc!=4)return 2;ifstream tf(argv[1]),cf(argv[2]);ofstream out(argv[3]);
 int q,b,w,t,m;string d;while(tf>>q>>b>>w>>d>>t)tab[q][b]={w,d=="R"?1:-1,t};while(cf>>q>>b>>m)contexts[q].push_back(m);
 long long pairs=0,tests=0;int survivors=0;
 for(int drop=0;drop<N;drop++){
   int incoming=0;bool uniform=true;
   for(int q=0;q<N;q++)for(int b=0;b<2;b++)if(tab[q][b].t==drop){int d=tab[q][b].d;if(incoming&&incoming!=d)uniform=false;incoming=d;}
   if(!uniform||!incoming)continue;int offset=-2*incoming;
   for(int keep=0;keep<N;keep++)if(keep!=drop){pairs++;bool good=true;
     for(int mask:contexts[drop]){tests++;int b=(mask>>R)&1;Row old=tab[drop][b];int goal=(mask&~(1<<R))|(old.w<<R),goalhead=old.d+(old.t==drop?offset:0),goalstate=old.t==drop?keep:old.t;
       int q=keep,h=offset,tape=mask;bool ok=false;
       for(int j=0;j<S;j++){
         if(q>=N||h< -R||h>R)break;int read=(tape>>(h+R))&1;Row r=tab[q][read];
         if(r.t==drop){r.t=keep;r.d=-r.d;}
         tape=(tape&~(1<<(h+R)))|(r.w<<(h+R));h+=r.d;q=r.t;
         if(q==goalstate&&h==goalhead&&tape==goal){ok=true;break;}
       }
       if(!ok){good=false;break;}
     }
     if(good){survivors++;out<<drop<<' '<<keep<<' '<<offset<<'\n';cout<<"SURVIVOR "<<drop<<' '<<keep<<' '<<offset<<'\n';}
   }
 }
 cout<<"pairs "<<pairs<<" tests "<<tests<<" survivors "<<survivors<<'\n';
}
