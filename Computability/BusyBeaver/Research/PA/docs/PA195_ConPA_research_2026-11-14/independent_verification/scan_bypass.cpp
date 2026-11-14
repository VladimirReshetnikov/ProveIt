#include <array>
#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <string>
using namespace std;
struct Row { int w,d,t; };
Row tab[256][2];
vector<int> ctx[256][2];
int N=196;
int R=2;
bool run(int drop,int key,Row patch,int mask,const set<int>& incoming) {
  int p=key/2,b=key%2;
  Row first=tab[p][b];
  int goalbits=(mask&~(1<<R))|(first.w<<R),goalhead=first.d;
  int secondread=(goalbits>>(goalhead+R))&1;
  Row second=tab[drop][secondread];
  goalbits=(goalbits&~(1<<(goalhead+R)))|(second.w<<(goalhead+R));
  goalhead+=second.d;int goalstate=second.t;
  int state=p,head=0,bits=mask;
  for(int i=0;i<64;i++) {
    if(state>=N||state==drop||head < -R||head>R)return false;
    int read=(bits>>(head+R))&1,k=2*state+read;
    if(k!=key && incoming.count(k)) return false;
    Row act=k==key?patch:tab[state][read];
    bits=(bits&~(1<<(head+R)))|(act.w<<(head+R));
    state=act.t;head+=act.d;
    if(state==goalstate&&head==goalhead&&bits==goalbits)return true;
  }
  return false;
}
int main(int argc,char**argv){
 if(argc!=5&&argc!=6)return 2;
 ifstream tf(argv[1]),cf(argv[2]);ofstream out(argv[3]);N=stoi(argv[4]);
 if(argc==6)R=stoi(argv[5]);
 int q,b,w,t,mask;string d;
 while(tf>>q>>b>>w>>d>>t)tab[q][b]={w,d=="R"?1:-1,t};
 while(cf>>q>>b>>mask)ctx[q][b].push_back(mask);
 long long triples=0,eligible=0,survivors=0;
 for(int drop=1;drop<N;drop++){
   if(tab[drop][0].t==drop||tab[drop][1].t==drop)continue;
   set<int> incoming;
   for(int p=0;p<N;p++)if(p!=drop)for(int b=0;b<2;b++)if(tab[p][b].t==drop)incoming.insert(2*p+b);
   if(incoming.empty())continue;
   eligible++;
   vector<vector<Row>> choices;bool fail=false;
   for(int key:incoming){
     int p=key/2,bit=key%2;vector<Row> valid;
     for(int dest=0;dest<=N;dest++)if(dest!=drop)for(int wr=0;wr<2;wr++)for(int dir:{-1,1}){
       triples++;Row patch={wr,dir,dest};bool ok=true;
       for(int mask:ctx[p][bit])if(!run(drop,key,patch,mask,incoming)){ok=false;break;}
       if(ok)valid.push_back(patch);
     }
     choices.push_back(valid);
     if(valid.empty()){fail=true;break;}
   }
   if(!fail){
     survivors++;out<<"DROP "<<drop<<" incoming "<<incoming.size()<<'\n';
     int j=0;
     for(int key:incoming){
       out<<"PATCH "<<key/2<<' '<<key%2<<" options "<<choices[j].size()<<'\n';
       for(Row a:choices[j])out<<a.w<<' '<<a.d<<' '<<a.t<<'\n';
       j++;
     }
     out.flush();
   }
 }
 cout<<"eligible "<<eligible<<" row_choices "<<triples<<" survivors "<<survivors<<'\n';
}
