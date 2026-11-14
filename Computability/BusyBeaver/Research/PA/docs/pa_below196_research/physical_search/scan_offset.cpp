// Displaced single-state projection; all incoming edges reverse direction.
#include <bitset>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Row{int w,d,t;};
int N,R;Row tab[256][2];vector<int>ctx[256][2];
int project(int q,int drop,int keep){return q==drop?keep:q;}
bool run(int drop,int keep,int off,int q,int bit,int mask,int pk,Row patch,bitset<512>* vis){
 Row o=tab[q][bit];int target=project(o.t,drop,keep),th=o.d+(o.t==drop?off:0),tt=(mask&~(1<<R))|(o.w<<R);
 int state=project(q,drop,keep),head=q==drop?off:0,tape=mask;
 for(int k=0;k<32;k++){
  if(state>=N||head< -R||head>R)return false;
  int b=(tape>>(head+R))&1,key=2*state+b;if(vis)vis->set(key);
  Row row=tab[state][b];if(row.t==drop){row.t=keep;row.d+=off;}
  if(key==pk)row=patch;
  tape=(tape&~(1<<(head+R)))|(row.w<<(head+R));head+=row.d;state=row.t;
  if(state==target&&head==th&&tape==tt)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=6)return 2;N=stoi(argv[4]);R=stoi(argv[5]);ifstream tf(argv[1]),cf(argv[2]);ofstream out(argv[3]);
 int q,b,w,t,mask;string d;while(tf>>q>>b>>w>>d>>t)tab[q][b]={w,d=="R"?1:-1,t};while(cf>>q>>b>>mask)ctx[q][b].push_back(mask);
 long long pairs=0,keys=0,patches=0,plain=0,passes=0;
 for(int drop=0;drop<N;drop++)for(int off:{-2,2}){
  bool allowed=true;int incoming=0;
  for(int q=0;q<N;q++)if(q!=drop)for(int b=0;b<2;b++)if(tab[q][b].t==drop){incoming++;if(tab[q][b].d+off!=1&&tab[q][b].d+off!= -1)allowed=false;}
  if(!allowed||!incoming)continue;
  for(int keep=0;keep<N;keep++)if(keep!=drop){
   pairs++;bitset<512> possible;possible.set();bool failure=false;
   for(int b=0;b<2;b++)for(int mask:ctx[drop][b]){
    bitset<512> vis;if(!run(drop,keep,off,drop,b,mask,-1,{},&vis)){failure=true;possible&=vis;}
    if(possible.none())break;
   }
   if(!failure){plain++;out<<"PLAIN "<<drop<<" "<<keep<<" "<<off<<endl;continue;}
   possible[2*drop]=possible[2*drop+1]=false;
   for(int key=0;key<2*N;key++)if(possible[key]){
    keys++;for(int dest=0;dest<=N;dest++)if(dest!=drop)for(int wr=0;wr<2;wr++)for(int dr:{-1,1}){
     patches++;Row patch{wr,dr,dest};bool ok=true;
     for(int orig:{drop,key/2}){
      for(int b=0;b<2;b++){
       for(int mask:ctx[orig][b])if(!run(drop,keep,off,orig,b,mask,key,patch,nullptr)){ok=false;break;}
       if(!ok)break;
      }if(!ok)break;
     }
     if(ok){passes++;out<<"PASS "<<drop<<" "<<keep<<" "<<off<<" "<<key<<" "<<wr<<" "<<dr<<" "<<dest<<endl;}
    }
   }
  }
 }
 cout<<"pairs "<<pairs<<" plain "<<plain<<" keys "<<keys<<" patches "<<patches<<" passes "<<passes<<endl;
}
