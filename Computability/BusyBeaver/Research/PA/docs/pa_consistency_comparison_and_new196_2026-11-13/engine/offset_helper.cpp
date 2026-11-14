// One-state offset fold, with one arbitrary extra retained-row repair.
#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <string>
#include <chrono>
using namespace std;
constexpr int N=196,R=4,S=64;
struct Row{int w,d,t;}; Row tab[N][2]; vector<int> contexts[N];
bool run(int drop,int keep,int offset,int orig,int mask,int key=-1,Row repair={},bitset<2*N>*visited=nullptr){
 int b=(mask>>R)&1;Row old=tab[orig][b];int goal=(mask&~(1<<R))|(old.w<<R),goalhead=old.d+(old.t==drop?offset:0),goalstate=old.t==drop?keep:old.t;
 int q=orig==drop?keep:orig,h=orig==drop?offset:0,tape=mask;
 for(int j=0;j<S;j++){
  if(q>=N||h< -R||h>R)return false;int read=(tape>>(h+R))&1,k=2*q+read;if(visited)visited->set(k);Row r=tab[q][read];
  if(r.t==drop){r.t=keep;r.d=-r.d;}
  if(k==key)r=repair;
  tape=(tape&~(1<<(h+R)))|(r.w<<(h+R));h+=r.d;q=r.t;
  if(q==goalstate&&h==goalhead&&tape==goal)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=4)return 2;ifstream tf(argv[1]),cf(argv[2]);ofstream out(argv[3]);
 int q,b,w,t,m;string d;while(tf>>q>>b>>w>>d>>t)tab[q][b]={w,d=="R"?1:-1,t};while(cf>>q>>b>>m)contexts[q].push_back(m);
 long long pairs=0,tests=0,keys=0;int survivors=0;
 auto start=chrono::steady_clock::now();
 for(int drop=0;drop<N;drop++){
   int incoming=0;bool uniform=true;
   for(int q=0;q<N;q++)for(int b=0;b<2;b++)if(tab[q][b].t==drop){int d=tab[q][b].d;if(incoming&&incoming!=d)uniform=false;incoming=d;}
   if(!uniform||!incoming)continue;int offset=-2*incoming;
   for(int keep=0;keep<N;keep++)if(keep!=drop){pairs++;bitset<2*N> possible;possible.set();bool failure=false;
    for(int mask:contexts[drop]){bitset<2*N> visited;if(!run(drop,keep,offset,drop,mask,-1,{},&visited)){possible &= visited;failure=true;}if(possible.none())break;}
    if(!failure){out<<"PLAIN "<<drop<<' '<<keep<<' '<<offset<<'\n';survivors++;continue;}
    possible.reset(2*drop);possible.reset(2*drop+1);
    for(int key=0;key<2*N;key++)if(possible[key]){keys++;int helper=key/2;
      for(int t=0;t<=N;t++)if(t!=drop)for(int w:{0,1})for(int d:{-1,1}){tests++;Row repair{w,d,t};bool good=true;
        for(int orig:{drop,helper})for(int mask:contexts[orig])if(good)good=run(drop,keep,offset,orig,mask,key,repair);
        if(good){survivors++;out<<"ONE "<<drop<<' '<<keep<<' '<<offset<<' '<<helper<<' '<<key%2<<' '<<w<<' '<<d<<' '<<t<<'\n';out.flush();cout<<"SURVIVOR "<<drop<<' '<<keep<<' '<<offset<<'\n';}
      }
    }
   }
   if(drop%20==19)cerr<<"drop "<<drop+1<<" pairs "<<pairs<<" tests "<<tests<<" survivors "<<survivors<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
 }
 cout<<"pairs "<<pairs<<" keys "<<keys<<" tests "<<tests<<" survivors "<<survivors<<'\n';
}
