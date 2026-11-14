#include <array>
#include <deque>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
using namespace std;
constexpr int K=10,INF=100000000;
struct DB{array<int,K*K>a{};bool bot=true;int&at(int i,int j){return a[i*K+j];}int get(int i,int j)const{return a[i*K+j];}};
struct Op{int kind,r,z,n;};
bool close(DB&d){
 if(d.bot)return false;
 for(int k=0;k<K;k++)for(int i=0;i<K;i++)if(d.get(i,k)<INF)for(int j=0;j<K;j++)if(d.get(k,j)<INF)
  d.at(i,j)=min(d.get(i,j),d.get(i,k)+d.get(k,j));
 for(int i=0;i<K;i++)if(d.get(i,i)<0){d.bot=true;return false;}
 return true;
}
DB guard(DB d,int r,bool z){
 if(d.bot)return d;
 if(z)d.at(r,9)=min(d.get(r,9),0);
 else d.at(9,r)=min(d.get(9,r),-1);
 close(d);return d;
}
DB shift(DB d,int r,int v){
 if(d.bot)return d;
 for(int j=0;j<K;j++)if(d.get(r,j)<INF)d.at(r,j)+=v;
 for(int i=0;i<K;i++)if(d.get(i,r)<INF)d.at(i,r)-=v;
 return d;
}
int main(){
 ifstream f("dbm_input.txt");int n;f>>n;vector<Op> ops(n);vector<bool> head(n,false);
 for(int i=0;i<n;i++){
  auto&o=ops[i];f>>o.kind>>o.r>>o.z>>o.n;
  for(int q:{o.z,o.n})if(q>=0 && (q==n||q<=i))head[q==n?0:q]=true;
 }
 vector<DB> states(n);vector<int> updates(n,0);vector<bool> pending(n,false);deque<int> todo;
 DB init;init.bot=false;int vs[K]={2,0,0,0,0,0,0,0,0,0};
 for(int i=0;i<K;i++)for(int j=0;j<K;j++)init.at(i,j)=vs[i]-vs[j];
 states[25]=init;todo.push_back(25);pending[25]=true;
 auto add=[&](int q,DB d){
  if(d.bot || q<0)return;if(q==n)q=0;
  DB old=states[q],joined=d;
  if(!old.bot){
   for(int k=0;k<K*K;k++){
    joined.a[k]=max(old.a[k],d.a[k]);
    if(head[q] && updates[q]>=3 && joined.a[k]>old.a[k])joined.a[k]=INF;
   }
   for(int i=0;i<9;i++)joined.at(9,i)=min(joined.get(9,i),0);
   close(joined);
  }
  if(old.bot || joined.a!=old.a){states[q]=joined;updates[q]++;if(!pending[q]){todo.push_back(q);pending[q]=true;}}
 };
 long steps=0;
 while(!todo.empty()){
  int pc=todo.front();todo.pop_front();pending[pc]=false;steps++;DB d=states[pc];Op o=ops[pc];
  if(o.kind==1)add(o.n,shift(d,o.r,1));
  if(o.kind==2){add(o.z,guard(d,o.r,true));add(o.n,shift(guard(d,o.r,false),o.r,-1));}
  if(o.kind==3)add(o.n,d);
  if(steps>10000000){cerr<<"too many\n";return 2;}
 }
 // Independent closure check using unwidened transfers.
 int checked=0;
 auto covered=[&](int q,DB d){if(d.bot||q<0)return true;if(q==n)q=0;const auto&t=states[q];if(t.bot)return false;for(int k=0;k<K*K;k++)if(d.a[k]>t.a[k])return false;checked++;return true;};
 for(int pc=0;pc<n;pc++){
  auto d=states[pc];auto o=ops[pc];bool ok=true;
  if(o.kind==1)ok=covered(o.n,shift(d,o.r,1));
  if(o.kind==2)ok=covered(o.z,guard(d,o.r,true))&&covered(o.n,shift(guard(d,o.r,false),o.r,-1));
  if(o.kind==3)ok=covered(o.n,d);
  if(!ok){cerr<<"not inductive "<<pc<<endl;return 3;}
 }
 ofstream out("dbm_certificate.txt");out<<n<<" "<<steps<<" "<<checked<<"\n";
 for(int pc=0;pc<n;pc++){
  out<<pc<<" "<<states[pc].bot;for(int x:states[pc].a)out<<" "<<x;out<<"\n";
 }
 cout<<"inductive states "<<n<<" iterations "<<steps<<" edges "<<checked<<endl;
}
