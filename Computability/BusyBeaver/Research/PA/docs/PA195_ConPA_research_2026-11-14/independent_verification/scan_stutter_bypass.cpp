#include <array>
#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <string>
using namespace std;
struct Row { int w,d,t; };
struct Config { int q,h,bits; };
Row tab[256][2];
vector<int> ctx[256][2];
int N=196,R=4,LIMIT=64;
vector<Config> parent_goals(int p,int mask,int drop) {
  int q=p,h=0,bits=mask; vector<Config> goals;
  for(int i=0;i<LIMIT;i++) {
    if(q>=N||h < -R||h>R)break;
    int read=(bits>>(h+R))&1;Row a=tab[q][read];
    bits=(bits&~(1<<(h+R)))|(a.w<<(h+R));q=a.t;h+=a.d;
    if(i>=1 && q!=drop)goals.push_back({q,h,bits});
  }
  return goals;
}
bool run(int drop,int key,Row patch,int mask,const set<int>& incoming,const vector<Config>& goals) {
  int state=key/2,head=0,bits=mask;
  for(int i=0;i<LIMIT;i++) {
    if(state>=N||state==drop||head < -R||head>R)return false;
    int read=(bits>>(head+R))&1,k=2*state+read;
    if(k!=key && incoming.count(k)) return false;
    Row act=k==key?patch:tab[state][read];
    bits=(bits&~(1<<(head+R)))|(act.w<<(head+R));
    state=act.t;head+=act.d;
    for(auto goal:goals)if(state==goal.q&&head==goal.h&&bits==goal.bits)return true;
  }
  return false;
}
int main(int argc,char**argv){
 if(argc!=5&&argc!=6)return 2;
 ifstream tf(argv[1]),cf(argv[2]);ofstream out(argv[3]);N=stoi(argv[4]);
 if(!tf||!cf||!out){cerr<<"Cannot open input or output file\n";return 2;}
 if(argc==6)R=stoi(argv[5]);
 int q,b,w,t,mask;string d;
 while(tf>>q>>b>>w>>d>>t)tab[q][b]={w,d=="R"?1:-1,t};
 int count=0;
 while(cf>>q>>b>>mask){ctx[q][b].push_back(mask);count++;}
 if(!count){cerr<<"Empty context input\n";return 2;}
 long long triples=0,eligible=0,survivors=0,firstpasses=0;
 for(int drop=1;drop<N;drop++){
   set<int> incoming;
   for(int p=0;p<N;p++)if(p!=drop)for(int b=0;b<2;b++)if(tab[p][b].t==drop)incoming.insert(2*p+b);
   if(incoming.empty())continue;
   eligible++;
   vector<vector<Row>> choices;bool fail=false;
   for(int key:incoming){
     int p=key/2,bit=key%2;vector<Row> valid;
     vector<vector<Config>> goals;
     for(int mask:ctx[p][bit])goals.push_back(parent_goals(p,mask,drop));
     for(int dest=0;dest<=N;dest++)if(dest!=drop)for(int wr=0;wr<2;wr++)for(int dir:{-1,1}){
       triples++;Row patch={wr,dir,dest};bool ok=true;int i=0;
       for(int mask:ctx[p][bit]){
         if(!run(drop,key,patch,mask,incoming,goals[i])){ok=false;break;}
         if(i==0)firstpasses++;
         i++;
       }
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
 cout<<"eligible "<<eligible<<" row_choices "<<triples<<" firstpasses "<<firstpasses<<" survivors "<<survivors<<'\n';
}
