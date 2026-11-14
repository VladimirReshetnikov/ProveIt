#include <iostream>
#include <fstream>
#include <vector>
#include <array>
#include <algorithm>
#include <chrono>
using namespace std;
struct Row {int w,d,n;};
struct Case {int q,b,mask;};
Row T[196][2];
vector<int> C[196][2];
int R=4,MAXSTEPS=64;
int SHIFT=0;
inline int proj(int q,int drop,int keep){return q==drop?keep:q;}
int check(int drop,int keep,int cr,Row patch,const Case &c,bool usepatch=true){
 int oldmask=c.mask; auto old=T[c.q][c.b];
 int gm=old.w ? (oldmask|(1<<R)) : (oldmask&~(1<<R));
 int gh=R+old.d+(old.n==drop?SHIFT:0),gq=proj(old.n,drop,keep);
 int mask=oldmask,h=R+(c.q==drop?SHIFT:0),q=keep;
 for(int k=1;k<=MAXSTEPS;k++){
  if(q==196||h<0||h>2*R)return 0;
  int b=(mask>>h)&1;
  auto a=T[q][b];
  if(a.n==drop)a.d=-a.d;
  if(usepatch&&q==keep&&b==cr)a=patch;
  mask=a.w?(mask|(1<<h)):(mask&~(1<<h));h+=a.d;q=proj(a.n,drop,keep);
  if(q==gq&&h==gh&&mask==gm)return k;
 }
 return 0;
}
int main(int argc,char**argv){
 if(argc!=4&&argc!=6)return 2;
 int onlydrop=argc==6?stoi(argv[4]):-1,onlykeep=argc==6?stoi(argv[5]):-1;
 ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n)T[q][b]={w,d=='R'?1:-1,n};
 ifstream cf(argv[2]);cf>>R;int len,x;
 while(cf>>q>>b>>len){for(int i=0;i<len;i++){cf>>x;C[q][b].push_back(x);}}
 MAXSTEPS=stoi(argv[3]);auto start=chrono::steady_clock::now();long long tested=0,passed=0;
 for(int drop=1;drop<196;drop++){
  if(onlydrop>=0&&drop!=onlydrop)continue;
  int incoming_dir=0; bool compatible=true;
  for(int p=0;p<196;p++)if(p!=drop)for(int b=0;b<2;b++)if(T[p][b].n==drop){
   if(incoming_dir&&incoming_dir!=T[p][b].d)compatible=false;
   incoming_dir=T[p][b].d;
  }
  if(!compatible||!incoming_dir)continue;
  SHIFT=-2*incoming_dir;
  for(int keep=0;keep<196;keep++)if(drop!=keep&&(onlykeep<0||keep==onlykeep)){
   vector<Case> first,full;
   for(int q0:{drop,keep})for(int b0:{0,1}){
    if(!C[q0][b0].empty())first.push_back({q0,b0,C[q0][b0][0]});
    for(int a:C[q0][b0])full.push_back({q0,b0,a});
   }
   for(int cr:{0,1})for(int n=0;n<=196;n++)if(n!=drop)for(int d:{-1,1})for(int w:{0,1}){
    tested++;Row p={w,d,n};bool ok=true;
    for(auto c:first)if(!check(drop,keep,cr,p,c)){ok=false;break;}
    if(!ok)continue;
    int longest=0;
    for(auto c:full){int k=check(drop,keep,cr,p,c);if(!k){ok=false;break;}longest=max(longest,k);}
    if(ok){passed++;cout<<"PASS "<<drop<<" "<<keep<<" "<<cr<<" "<<w<<" "<<d<<" "<<n<<" "<<longest<<" "<<SHIFT<<"\n"<<flush;}
   }
  }
  if(drop%25==24)cerr<<"completed "<<drop+1<<" states, "<<tested<<" patches\n";
 }
 auto dur=chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now()-start).count();
 cout<<"DONE "<<tested<<" "<<passed<<" "<<R<<" "<<MAXSTEPS<<" "<<dur<<"\n";
}
