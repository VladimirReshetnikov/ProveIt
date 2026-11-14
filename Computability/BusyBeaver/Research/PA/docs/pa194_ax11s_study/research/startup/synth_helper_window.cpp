#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;bool operator==(A b)const{return w==b.w&&d==b.d&&n==b.n;}};
array<A,2> base[4000];bool ex[4000];vector<int>qs;
int K=3,B=60;
int code(A a){return (a.n*2+(a.d==1))*2+a.w;}
bool test(A action,int mq,int mb,A mutation,int init){
 int q=88,h=0,tape=init;bool b=init>>K&1,p=init>>(K-1)&1;int goal=b?103:(p?122:45);
 for(int st=0;st<B;st++){
  if(st&&q==goal&&h==1&&tape==init)return true;
  if(h < -K||h>K||!ex[q])return false;
  int bit=tape>>(h+K)&1;A a=(q==88&&!bit)?action:((q==mq&&bit==mb)?mutation:base[q][bit]);
  tape=(tape&~(1<<(h+K)))|(a.w<<(h+K));h+=a.d;q=a.n;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc>2)K=stoi(argv[2]);if(argc>3)B=stoi(argv[3]);ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n){if(q==301)continue;if(!ex[q])qs.push_back(q);ex[q]=1;base[q][b]={w,d=='R'?1:-1,n==301?88:n};}
 vector<int>patterns; for(int p=0;p<(1<<(2*K+1));p++) patterns.push_back(p);
 stable_sort(patterns.begin(),patterns.end(),[](int a,int b){return __builtin_popcount(a)<__builtin_popcount(b);});
 long long trials=0,solutions=0;set<tuple<int,int,int,int>>printed;
 for(int h:qs)for(int hw=0;hw<2;hw++)for(int hd:{-1,1}){
  A action={hw,hd,h};set<pair<int,int>> mutable_rows;
  int initial=-1;for(int pat:patterns)if(!test(action,-1,-1,{0,1,0},pat)){initial=pat;break;}
  if(initial==-1){cerr<<"ACTION ALONE "<<hw<<" "<<hd<<" "<<h<<"\n";continue;}
  int initial_goal=(initial>>K&1)?103:((initial>>(K-1)&1)?122:45);
  int q=88,x=0,tape=initial;
  for(int st=0;st<B;st++){
   if(st&&q==initial_goal&&x==1&&tape==initial)break;
   if(x < -K||x>K||!ex[q])break;
   int bit=tape>>(x+K)&1;
   if(!(q==88&&bit==0)) mutable_rows.emplace(q,bit);
   A a=q==88&&bit==0?action:base[q][bit];tape=(tape&~(1<<(x+K)))|(a.w<<(x+K));x+=a.d;q=a.n;
  }
  for(auto [mq,mb]:mutable_rows)for(int wr=0;wr<2;wr++)for(int dr:{-1,1})for(int nr:qs){
   A mut={wr,dr,nr};trials++;bool ok=true;
   for(int init:patterns)if(!test(action,mq,mb,mut,init)){ok=false;break;}
   if(ok&&printed.emplace(code(action),mq,mb,code(mut)).second){solutions++;cout<<hw<<' '<<hd<<' '<<h<<' '<<mq<<' '<<mb<<' '<<wr<<' '<<dr<<' '<<nr<<'\n';}
  }
 }
 cerr<<"radius "<<K<<" bound "<<B<<" trials "<<trials<<" solutions "<<solutions<<'\n';
}
