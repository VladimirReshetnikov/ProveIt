// Exact direct contraction through two removed controls.
#include <array>
#include <fstream>
#include <iostream>
#include <vector>
#include <string>
using namespace std;
struct Row {int w,d,t; bool operator==(const Row&b)const{return w==b.w&&d==b.d&&t==b.t;}};
Row table[256][2];vector<int> contexts[256][2];int N,R;
bool parentblock(int p,int bit,int mask,int a,int b,Row &patch){
 if(((mask>>R)&1)!=bit)return false;
 int state=p,head=0,tape=mask;
 for(int k=0;k<64;k++){
   if(state>=N||head< -R||head>R)return false;
   int read=(tape>>(head+R))&1;Row act=table[state][read];
   tape=(tape&~(1<<(head+R)))|(act.w<<(head+R));head+=act.d;state=act.t;
   if(state!=a&&state!=b){
     if(head!=1&&head!=-1)return false;
     if((tape&~(1<<R))!=(mask&~(1<<R)))return false;
     patch={(tape>>R)&1,head,state};return true;
   }
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=6)return 2;
 N=stoi(argv[4]);R=stoi(argv[5]);
 ifstream tf(argv[1]),cf(argv[2]);ofstream out(argv[3]);
 int q,bit,w,t,mask;string d;
 while(tf>>q>>bit>>w>>d>>t)table[q][bit]={w,d=="R"?1:-1,t};
 while(cf>>q>>bit>>mask)contexts[q][bit].push_back(mask);
 long long pairs=0,incoming_count=0,blocks=0,survivors=0;
 for(int a=1;a<N;a++)for(int b=a+1;b<N;b++){
   pairs++;bool ok=true;vector<pair<int,Row>> patches;
   for(int p=0;p<N&&ok;p++)if(p!=a&&p!=b)for(int read=0;read<2&&ok;read++)if(table[p][read].t==a||table[p][read].t==b){
     incoming_count++;bool have=false;Row choice={};
     for(int m:contexts[p][read]){
       blocks++;Row candidate;
       if(!parentblock(p,read,m,a,b,candidate)){ok=false;break;}
       if(!have){choice=candidate;have=true;}
       else if(!(candidate==choice)){ok=false;break;}
     }
     if(!have){ok=false;break;}
     patches.push_back({2*p+read,choice});
   }
   if(ok&&!patches.empty()){
     survivors++;out<<"DROP "<<a<<' '<<b<<" patches "<<patches.size()<<'\n';
     for(auto pr:patches){Row x=pr.second;out<<pr.first/2<<' '<<pr.first%2<<' '<<x.w<<' '<<x.d<<' '<<x.t<<'\n';}
     out.flush();
   }
 }
 cout<<"pairs "<<pairs<<" incoming_screened "<<incoming_count<<" blocks "<<blocks<<" survivors "<<survivors<<'\n';
}
