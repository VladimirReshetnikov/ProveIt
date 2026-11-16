#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using namespace std;
struct Row{int w,d,n;};
constexpr int N=196,DROP=45,KEEP=160,HELPER=184,MAX=512;
struct Tape{
 vector<uint64_t> a; int64_t bias;
 Tape():a(65536),bias(2097152){}
 int get(int64_t p)const{p+=bias;if(p<0||p>=int64_t(a.size()*64))throw 1;return (a[p>>6]>>(p&63))&1;}
 void put(int64_t p,int b){p+=bias;if(p<0||p>=int64_t(a.size()*64))throw 1;uint64_t m=uint64_t(1)<<(p&63);if(b)a[p>>6]|=m;else a[p>>6]&=~m;}
 uint64_t consume(int64_t &p,int b,int w,int d,uint64_t limit){
  uint64_t total=0;
  while(total<limit){int64_t i=p+bias;if(i<0||i>=int64_t(a.size()*64))throw 1;
   uint64_t &word=a[i>>6];int bit=i&63;int len=d==1?64-bit:bit+1;
   if(uint64_t(len)>limit-total)len=limit-total;
   uint64_t mask=len==64?~uint64_t(0):((uint64_t(1)<<len)-1);if(d==1)mask<<=bit;else mask<<=(bit-len+1);
   uint64_t bad=(b?~word:word)&mask;
   if(bad){int stop=d==1?__builtin_ctzll(bad):63-__builtin_clzll(bad);len=d==1?stop-bit:bit-stop;
    mask=len==0?0:((uint64_t(1)<<len)-1);if(d==1)mask<<=bit;else mask<<=(bit-len+1);}
   if(w)word|=mask;else word&=~mask;p+=int64_t(d)*len;total+=len;
   if(bad)break;
  }return total;
 }
};
int project(int q){return q==DROP?KEEP:q;}
void dump_tape(const Tape &a,int64_t head){
 bool inside=false;int64_t lo=0;cout<<"ones_runs";
 for(int64_t p=-a.bias;p<int64_t(a.a.size()*64)-a.bias;p++){
  bool one=a.get(p);if(one&&!inside){lo=p;inside=true;}if(!one&&inside){cout<<' '<<lo-head<<':'<<p-1-head;inside=false;}}
 if(inside){cout<<' '<<lo-head<<':'<<int64_t(a.a.size()*64)-a.bias-1-head;}cout<<"\n";
}
int block(const Row t[N][2],int q,int64_t h,const Tape &a){
 auto old=t[q][a.get(h)];int goal=project(old.n);int64_t goalh=h+old.d;map<int64_t,int> want,delta;
 if(old.w!=a.get(h))want[h]=old.w;
 int state=project(q);int64_t p=h;
 for(int k=1;k<=MAX;k++){
  if(state==196)return 0;
  auto it=delta.find(p);int bit=it==delta.end()?a.get(p):it->second;
  Row r=(state==HELPER&&bit==1)?Row{1,-1,75}:t[state][bit];
  if(r.w==a.get(p))delta.erase(p);else delta[p]=r.w;p+=r.d;state=project(r.n);
  if(state==goal&&p==goalh&&delta==want)return k;
 }return 0;
}
int main(int argc,char**argv){if(argc!=3)return 1;Row t[N][2];bool seen[N][2]={};ifstream f(argv[1]);int q,b,w,n;char d;int count=0;while(f>>q>>b>>w>>d>>n){if(q<0||q>=N||b<0||b>1||w<0||w>1||(d!='R'&&d!='L')||n<0||n>N||seen[q][b])return 2;seen[q][b]=true;t[q][b]={w,d=='R'?1:-1,n};count++;}if(count!=392)return 3;
 uint64_t bound=stoull(argv[2]),k=0,child=0,skipped=0;array<uint64_t,N> visits{};Tape a;int64_t head=0;q=0;
 while(k<bound){if(q==N){cout<<"halt parent "<<k<<" child "<<child<<"\n";return 0;}
  if(q==DROP||q==KEEP||q==HELPER){visits[q]++;int m=block(t,q,head,a);if(!m){
   int mask=0;for(int i=-2;i<=2;i++)mask|=a.get(head+i)<<(i+2);
   cout<<"failure parent "<<k<<" child "<<child<<" state "<<q<<" head "<<head<<" read "<<a.get(head)<<" mask "<<mask<<" visits45 "<<visits[45]<<" visits160 "<<visits[160]<<" visits184 "<<visits[184]<<" sweepsteps "<<skipped<<"\n";
   // Output finite-support tape as inclusive runs of ones, relative to head.
   dump_tape(a,head);return 0;
  }child+=m;
  }else if(t[q][a.get(head)].n==q){Row r=t[q][a.get(head)];uint64_t m=a.consume(head,a.get(head),r.w,r.d,bound-k);if(!m)return 4;k+=m;child+=m;skipped+=m;continue;
  }else child++;
  Row r=t[q][a.get(head)];a.put(head,r.w);head+=r.d;q=r.n;k++;
 }
 cout<<"limit "<<k<<" child "<<child<<" q "<<q<<" h "<<head<<" sweepsteps "<<skipped<<"\n";
 dump_tape(a,head);
 return 0;
}
