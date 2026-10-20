#include <array>
#include <vector>
#include <map>
#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <cstring>
using namespace std;
struct A{int w,d,t; bool operator==(const A&o)const{return w==o.w&&d==o.d&&t==o.t;}};
const int N=1024,R=6,L=48;
A base[N][2]; bool exists[N]; int fact[N][2*R+1];
vector<int> states; int startq=0,haltq=254;
int phi(int q,int keep,int drop){return q==drop?keep:q;}
struct C {array<int,2*L+1> initial,target;int z,h,b;};
vector<C> contracts[2];
int local(C&c,int keep,int drop,A a0,A a1,int known,int limit){
 auto tape=c.initial; int q=keep,h=0;
 for(int n=1;n<=limit;n++){
  if(h< -L||h>L||q==haltq||!exists[q]||tape[h+L]<0)return 0;
  int b=tape[h+L];A a=base[q][b];
  if(q==keep){if(known>=0&&b!=known)return 2;a=b?a1:a0;}
  tape[h+L]=a.w;h+=a.d;q=phi(a.t,keep,drop);
  if(q==c.z&&h==c.h&&tape==c.target)return 1;
 }
 return 0;
}
void prepare(int keep,int drop){
 for(int b=0;b<2;b++)contracts[b].clear();
 for(int q:{keep,drop})for(int b=0;b<2;b++){
  if(!(fact[q][R]&(1<<b)))continue;
  C c;c.initial.fill(-1);
  for(int k=-R;k<=R;k++){int f=fact[q][k+R];if(f==1||f==2)c.initial[k+L]=(f==2);}
  c.initial[L]=b;c.target=c.initial;c.target[L]=base[q][b].w;
  c.h=base[q][b].d;c.z=phi(base[q][b].t,keep,drop);c.b=b;
  contracts[b].push_back(c);
 }
}
int main(int argc,char**argv){
 if(argc<2)return 1;ifstream in(argv[1]);string line;
 while(getline(in,line)){if(line.rfind("#! start ",0)==0){startq=stoi(line.substr(9));continue;}if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,t;char d;s>>q>>b>>w>>d>>t;base[q][b]={w,d=='R'?1:-1,t};exists[q]=true;}
 for(int q=0;q<N;q++)if(exists[q])states.push_back(q);
 for(int k=0;k<2*R+1;k++)fact[startq][k]=3;
 bool changed=true;int rounds=0;
 while(changed){changed=false;rounds++;for(int q:states){if(!fact[q][R])continue;for(int b=0;b<2;b++)if(fact[q][R]&(1<<b)){
   auto a=base[q][b];if(a.t==haltq)continue;
   for(int k=-R;k<=R;k++){int j=k+a.d;int v=j==0?(1<<a.w):(j<-R||j>R?3:fact[q][j+R]);int &f=fact[a.t][k+R];if((f|v)!=f){f|=v;changed=true;}}
  }}}
 cerr<<"states "<<states.size()<<" rounds "<<rounds<<" facts ";int nf=0;for(int q:states)for(int k=0;k<2*R+1;k++)nf+=fact[q][k]==1||fact[q][k]==2;cerr<<nf<<"\n";
 vector<A> acts;for(int q:states)for(int w:{0,1})for(int d:{-1,1})acts.push_back({w,d,q});
 int count=0,pairs=0,withcand=0;long combos=0;int limit=argc>2?stoi(argv[2]):20;
 if(argc>3 && string(argv[3])=="neutral"){
  for(int q:states)for(int b=0;b<2;b++){
   prepare(q,q);if(contracts[b].empty())continue;
   for(A a:acts){if(a==base[q][b])continue;A aa[2]={base[q][0],base[q][1]};aa[b]=a;
    bool good=true;for(C&c:contracts[b])if(local(c,q,q,aa[0],aa[1],-1,limit)!=1){good=false;break;}
    if(good)cout<<q<<" "<<b<<" "<<a.w<<" "<<a.d<<" "<<a.t<<"\n";
   }
  }
  return 0;
 }
 for(int keep:states)if(keep!=startq)for(int drop:states)if(drop>keep&&drop!=startq){
  pairs++;prepare(keep,drop);vector<A> cand[2];
  for(int b=0;b<2;b++){
   for(A a:acts){if(a.t==drop)continue;bool good=true;for(C&c:contracts[b])if(!local(c,keep,drop,a,a,b,limit)){good=false;break;}if(good)cand[b].push_back(a);}
   if(cand[b].empty())break;
  }
  if(cand[0].empty()||cand[1].empty())continue;withcand++;
  for(A a0:cand[0])for(A a1:cand[1]){
   combos++;bool good=true;for(int b=0;b<2&&good;b++)for(C&c:contracts[b])if(local(c,keep,drop,a0,a1,-1,limit)!=1){good=false;break;}
   if(good){cout<<"FOLD "<<keep<<" "<<drop<<" "<<a0.w<<" "<<a0.d<<" "<<a0.t<<" "<<a1.w<<" "<<a1.d<<" "<<a1.t<<"\n";cout.flush();count++;}
  }
 }
 cerr<<"pairs "<<pairs<<" withcand "<<withcand<<" combos "<<combos<<" folds "<<count<<"\n";
 ofstream f("last_facts.txt");for(int q:states)for(int k=-R;k<=R;k++)if(fact[q][k+R]==1||fact[q][k+R]==2)f<<q<<" "<<k<<" "<<(fact[q][k+R]==2)<<"\n";
}
