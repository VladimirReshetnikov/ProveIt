#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;bool operator==(A b)const{return w==b.w&&d==b.d&&n==b.n;}};
array<A,2> old[4000],base[4000];bool ex[4000];vector<int>qs,pat[4000][2];set<int>boxes{0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
int K=4,B=100;
int code(A a){return (a.n*2+(a.d==1))*2+a.w;}
struct Case{int q,p,tq,th,tt;};
bool test(A action,int mq,int mb,A mutation,Case c,set<pair<int,int>>*trace=nullptr){
 int q=c.q==301?88:c.q,h=0,tape=c.p;
 for(int st=0;st<B;st++){
  if(st&&q==c.tq&&h==c.th&&tape==c.tt)return true;
  if(h < -K||h>K||!ex[q])return false;
  int bit=tape>>(h+K)&1;
  if(trace&&!(q==88&&bit==0)&&!boxes.count(q))trace->emplace(q,bit);
  A a=(q==88&&!bit)?action:((q==mq&&bit==mb)?mutation:base[q][bit]);
  tape=(tape&~(1<<(h+K)))|(a.w<<(h+K));h+=a.d;q=a.n;
 }
 return false;
}
Case makecase(int q,int p){A a=old[q][p>>K&1];return {q,p,a.n==301?88:a.n,a.d,(p&~(1<<K))|(a.w<<K)};}
int main(int argc,char**argv){
 if(argc>3)K=stoi(argv[3]);if(argc>4)B=stoi(argv[4]);ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n){old[q][b]={w,d=='R'?1:-1,n};if(q==301)continue;if(!ex[q])qs.push_back(q);ex[q]=1;base[q][b]={w,d=='R'?1:-1,n==301?88:n};}
 ifstream pf(argv[2]);int p;while(pf>>q>>p)pat[q][p>>K&1].push_back(p);
 vector<Case> cases;for(int q:{301,88})for(int b:{0,1})for(int p:pat[q][b])cases.push_back(makecase(q,p));
 long long trials=0,solutions=0;set<tuple<int,int,int,int>>printed;
 for(int h:qs)for(int hw=0;hw<2;hw++)for(int hd:{-1,1}){
  A action={hw,hd,h};set<pair<int,int>>mutable_rows;bool found=false;
  for(Case c:cases)if(!test(action,-1,-1,{0,1,0},c)){
   test(action,-1,-1,{0,1,0},c,&mutable_rows);found=true;break;}
  if(!found){cerr<<"ACTION ALONE "<<hw<<" "<<hd<<" "<<h<<"\n";continue;}
  for(auto [mq,mb]:mutable_rows)for(int wr=0;wr<2;wr++)for(int dr:{-1,1})for(int nr:qs){
   if(pat[mq][mb].empty())continue;
   A mut={wr,dr,nr};trials++;bool ok=true;
   for(Case c:cases)if(!test(action,mq,mb,mut,c)){ok=false;break;}
   if(ok)for(int p:pat[mq][mb])if(!test(action,mq,mb,mut,makecase(mq,p))){ok=false;break;}
   if(ok&&printed.emplace(code(action),mq,mb,code(mut)).second){solutions++;cout<<hw<<' '<<hd<<' '<<h<<' '<<mq<<' '<<mb<<' '<<wr<<' '<<dr<<' '<<nr<<'\n';}
  }
 }
 cerr<<"radius "<<K<<" bound "<<B<<" trials "<<trials<<" solutions "<<solutions<<'\n';
}
