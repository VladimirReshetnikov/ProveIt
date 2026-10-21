// Bounded coordinated repair of the primary K215 near miss: eliminate state40,
// reroute 27/1 and198/0, synthesize54/0 and one additional row.
// The additional row must independently preserve its original invariant contexts.
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <tuple>
#include <vector>
using namespace std;
struct Tr {int w,d,t;};struct C{int q,h,m;};struct Test{int origin,b,m;vector<C> old;};
Tr T[1024][2],U[1024][2];vector<int> states,masks[1024];int R,Start,Halt,Cap;
bool cut[1024][2];
vector<C> old_trace(int q,int m) {
 int h=0;vector<C> out;
 for(int n=0;n<Cap;n++){
  int j=h+R;if(j<0||j>2*R||q==Halt)break;int b=(m>>j)&1;
  if(n&&cut[q][b])break;
  Tr a=T[q][b];m=(m&~(1<<j))|(a.w<<j);h+=a.d;q=a.t;
  if(q!=40)out.push_back({q,h,m});
 }return out;
}
bool check(const Test& c,bool allow54) {
 int q=c.origin,h=0,m=c.m;
 for(int n=0;n<Cap;n++){
  int j=h+R;if(j<0||j>2*R||q==Halt||q==40)return false;int b=(m>>j)&1;
  if(n&&cut[q][b]&& !(allow54 && q==54&&b==0)) return false;
  Tr a=U[q][b];m=(m&~(1<<j))|(a.w<<j);h+=a.d;q=a.t;
  if(q==40)return false;
  for(auto g:c.old)if(q==g.q&&h==g.h&&m==g.m)return true;
 }return false;
}
vector<Test> cases(int q,int b){vector<Test>a;for(int m:masks[q])if(((m>>R)&1)==b)a.push_back({q,b,m,old_trace(q,m)});stable_sort(a.begin(),a.end(),[](const Test&a,const Test&b){return a.old.size()<b.old.size();});return a;}
bool all(const vector<Test>&v,bool allow54=false){for(auto&x:v)if(!check(x,allow54))return false;return true;}
int main(int argc,char**argv){
 ifstream f(argv[1]);int ns;f>>R>>Start>>Halt>>ns;Cap=argc>2?stoi(argv[2]):96;
 for(int i=0;i<ns;i++){int q,n;f>>q;states.push_back(q);for(int b=0;b<2;b++)f>>T[q][b].w>>T[q][b].d>>T[q][b].t;f>>n;for(int j=0;j<n;j++){int m;f>>m;masks[q].push_back(m);}}
 vector<Tr> actions;vector<int>targets=states;targets.push_back(Halt);for(int t:targets)if(t!=40)for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,t});
 unsigned long long provider_trials=0,providers=0,root_trials=0,hits=0;
 auto began=chrono::steady_clock::now();cout<<"{\"radius\":"<<R<<",\"cap\":"<<Cap<<",\"hits\":[";bool hf=true;
 for(int route:{54,66})for(int provider:states)if(provider!=40)for(int pb=0;pb<2;pb++){
  if((provider==27&&pb==1)||(provider==198&&pb==0)||(provider==54&&pb==0))continue;
  for(int q:states)for(int b=0;b<2;b++){U[q][b]=T[q][b];cut[q][b]=T[q][b].t==40;}
  U[27][1]={0,-1,302};U[198][0]={1,-1,route};
  // Provider row may be used internally after resynthesis. Its own old-context
  // proof must stop before the as-yet unsynthesized54/0.
  auto pc=cases(provider,pb),a27=cases(27,1),a198=cases(198,0),root=cases(54,0);
  for(auto pa:actions){
   provider_trials++;U[provider][pb]=pa;
   if(!all(pc)||!all(a27)||!all(a198))continue;providers++;
   for(auto ra:actions){
    root_trials++;U[54][0]=ra;
    if(!all(root,true))continue;
    // all changed entry contexts are rechecked under the joint table.
    if(!all(pc,true)||!all(a27,true)||!all(a198,true))continue;
    hits++;if(!hf)cout<<",";hf=false;
    cout<<"{\"route198\":"<<route<<",\"provider\":["<<provider<<","<<pb<<","<<pa.w<<","<<pa.d<<","<<pa.t<<"],\"root54\":["<<ra.w<<","<<ra.d<<","<<ra.t<<"]}";cout.flush();
   }
   U[54][0]=T[54][0];
  }
 }
 cout<<"],\"summary\":{\"provider_trials\":"<<provider_trials<<",\"providers\":"<<providers<<",\"root_trials\":"<<root_trials<<",\"hits\":"<<hits<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<"}}\n";
}
