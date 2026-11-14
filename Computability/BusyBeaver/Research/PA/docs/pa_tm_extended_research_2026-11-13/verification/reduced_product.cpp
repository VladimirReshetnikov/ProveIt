#include <array>
#include <deque>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <chrono>
using namespace std;
constexpr int K=10,INF=100000000;
struct DB {array<int,100>a{};bool bot=true;int& at(int i,int j){return a[10*i+j];}int get(int i,int j)const{return a[10*i+j];}};
struct State {DB d;array<uint64_t,8>s{};};
struct Op {int kind,r,z,n;};
bool has(const State&v,int m){return (v.s[m/64]>>(m%64))&1;}
void put(State&v,int m){v.s[m/64]|=uint64_t(1)<<(m%64);}
bool empty(const State&v){for(auto x:v.s)if(x)return false;return true;}
int count(const State&v){int ans=0;for(auto x:v.s)ans+=__builtin_popcountll(x);return ans;}
void close(DB&d){if(d.bot)return;for(int k=0;k<K;k++)for(int i=0;i<K;i++)if(d.get(i,k)<INF)for(int j=0;j<K;j++)if(d.get(k,j)<INF)d.at(i,j)=min(d.get(i,j),d.get(i,k)+d.get(k,j));for(int i=0;i<K;i++)if(d.get(i,i)<0){d.bot=true;return;}}
void reduce(State&v){
 if(v.d.bot||empty(v)){v.d.bot=true;v.s.fill(0);return;}
 bool change=true;
 while(change){
  change=false;int all=511,any=0;
  for(int m=0;m<512;m++)if(has(v,m)){all&=m;any|=m;}
  for(int r=0;r<9;r++){
   v.d.at(9,r)=min(v.d.get(9,r),0);
   if(!(any&(1<<r)))v.d.at(r,9)=min(v.d.get(r,9),0);
   if(all&(1<<r))v.d.at(9,r)=min(v.d.get(9,r),-1);
  }
  close(v.d);if(v.d.bot){v.s.fill(0);return;}
  for(int m=0;m<512;m++)if(has(v,m)){
   bool ok=true;
   for(int r=0;r<9&&ok;r++){
    bool pos=(m>>r)&1;
    if((pos&&v.d.get(r,9)<=0)||(!pos&&v.d.get(9,r)<=-1)){ok=false;break;}
    if(pos)for(int s=0;s<9;s++)if(v.d.get(r,s)<=0&&!((m>>s)&1)){ok=false;break;}
   }
   if(!ok){v.s[m/64]&=~(uint64_t(1)<<(m%64));change=true;}
  }
  if(empty(v)){v.d.bot=true;return;}
 }
}
State guard(State v,int r,bool z){if(v.d.bot)return v;for(int m=0;m<512;m++)if(has(v,m)&&bool((m>>r)&1)==z)v.s[m/64]&=~(uint64_t(1)<<(m%64));if(z)v.d.at(r,9)=min(v.d.get(r,9),0);else v.d.at(9,r)=min(v.d.get(9,r),-1);reduce(v);return v;}
State shift(State v,int r,int delta){
 if(v.d.bot)return v;auto old=v.s;v.s.fill(0);
 for(int m=0;m<512;m++)if((old[m/64]>>(m%64))&1){if(delta==1)put(v,m|(1<<r));else{put(v,m);put(v,m&~(1<<r));}}
 for(int j=0;j<K;j++)if(v.d.get(r,j)<INF)v.d.at(r,j)+=delta;
 for(int i=0;i<K;i++)if(v.d.get(i,r)<INF)v.d.at(i,r)-=delta;
 reduce(v);return v;
}
void join(State&to,const State&from){if(from.d.bot)return;if(to.d.bot){to=from;return;}for(int k=0;k<100;k++)to.d.a[k]=max(to.d.a[k],from.d.a[k]);for(int k=0;k<8;k++)to.s[k]|=from.s[k];}
bool equal(const State&a,const State&b){return a.d.bot==b.d.bot&&(a.d.bot||(a.d.a==b.d.a&&a.s==b.s));}
bool included(const State&a,const State&b){if(a.d.bot)return true;if(b.d.bot)return false;for(int k=0;k<100;k++)if(a.d.a[k]>b.d.a[k])return false;for(int k=0;k<8;k++)if(a.s[k]&~b.s[k])return false;return true;}
int main(){
 ifstream f("reduced_input.txt");int n;f>>n;vector<Op>ops(n);for(auto&o:ops)f>>o.kind>>o.r>>o.z>>o.n;vector<State>vs(n);
 for(int i=0;i<n;i++){int pc,bot;f>>pc>>bot;if(pc!=i)return 2;vs[i].d.bot=bot;for(auto&x:vs[i].d.a)f>>x;for(auto&x:vs[i].s)f>>x;reduce(vs[i]);}
 State init;init.d.bot=false;int v0[K]={2};for(int i=0;i<K;i++)for(int j=0;j<K;j++)init.d.at(i,j)=v0[i]-v0[j];put(init,1);
 auto start=chrono::steady_clock::now();bool fixed=false;int round=0;
 for(round=1;round<=200;round++){
  vector<State>next(n);join(next[25],init);
  auto add=[&](int q,State v){if(q<0||v.d.bot)return;if(q==n)q=0;join(next[q],v);};
  for(int pc=0;pc<n;pc++){
   auto v=vs[pc];auto o=ops[pc];
   if(o.kind==1)add(o.n,shift(v,o.r,1));
   if(o.kind==2){add(o.z,guard(v,o.r,true));add(o.n,shift(guard(v,o.r,false),o.r,-1));}
   if(o.kind==3)add(o.n,v);
  }
  int changed=0,np=0,bottom=0,newzeros=0;
  for(int pc=0;pc<n;pc++){
   if(!next[pc].d.bot&&!vs[pc].d.bot){
    for(int k=0;k<100;k++)next[pc].d.a[k]=min(next[pc].d.a[k],vs[pc].d.a[k]);
    for(int k=0;k<8;k++)next[pc].s[k]&=vs[pc].s[k];
   }else if(vs[pc].d.bot){next[pc].d.bot=true;next[pc].s.fill(0);}
   reduce(next[pc]);changed+=!equal(vs[pc],next[pc]);np+=count(next[pc]);bottom+=next[pc].d.bot;
   if(!next[pc].d.bot&&!vs[pc].d.bot)for(int r=0;r<9;r++)if(next[pc].d.get(r,9)<=0&&vs[pc].d.get(r,9)>0)newzeros++;
  }
  vs.swap(next);double sec=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  cout<<"round "<<round<<" changed "<<changed<<" patterns "<<np<<" bottom "<<bottom<<" newzeros "<<newzeros<<" seconds "<<sec<<endl;
  if(!changed){fixed=true;break;}if(sec>150)break;
 }
 // Strong check: each individually reduced image lies inside target.
 int bad=0,edges=0;auto chk=[&](int pc,int q,State v){if(q<0||v.d.bot)return;if(q==n)q=0;edges++;if(!included(v,vs[q])){if(bad<10)cerr<<"not included "<<pc<<" -> "<<q<<endl;bad++;}};
 for(int pc=0;pc<n;pc++){auto v=vs[pc];auto o=ops[pc];if(o.kind==1)chk(pc,o.n,shift(v,o.r,1));if(o.kind==2){chk(pc,o.z,guard(v,o.r,true));chk(pc,o.n,shift(guard(v,o.r,false),o.r,-1));}if(o.kind==3)chk(pc,o.n,v);}
 if(!included(init,vs[25])){cerr<<"initial missing\n";return 4;}
 ofstream out("reduced_certificate.txt");out<<n<<" "<<round<<" "<<edges<<" "<<bad<<"\n";for(int pc=0;pc<n;pc++){out<<pc<<" "<<vs[pc].d.bot;for(auto x:vs[pc].d.a)out<<" "<<x;for(auto x:vs[pc].s)out<<" "<<x;out<<"\n";}
 cout<<"FINAL fixed "<<fixed<<" bad "<<bad<<" edges "<<edges<<endl;return bad?3:0;
}
