#include <array>
#include <vector>
#include <queue>
#include <fstream>
#include <iostream>
#include <sstream>
#include <cstdlib>
using namespace std;
struct A{int w,d,n;};struct C{int q,h,t;};struct Case{int t;vector<C>goals;};
bool eq(C a,C b){return a.q==b.q&&a.h==b.h&&a.t==b.t;}
int main(int argc,char**argv){if(argc<2)return 2;int K=argc>2?atoi(argv[2]):5,L=argc>3?atoi(argv[3]):8,M=argc>4?atoi(argv[4]):64,W=2*K+1,N=1<<W,MASK=N-1,S=0,q,b,w,n;char d;string line;vector<array<A,2>>rows(5000);vector<bool>present(5000);ifstream in(argv[1]);while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};present[q]=true;S=max(S,q+1);}for(q=0;q<S;q++)if(!present[q])return 3;
 vector<vector<bool>>seen(S,vector<bool>(N));queue<pair<int,int>>todo;auto add=[&](int q,int t){if(q<S&&!seen[q][t]){seen[q][t]=true;todo.emplace(q,t);}};add(0,0);while(!todo.empty()){auto[q,t]=todo.front();todo.pop();auto a=rows[q][t>>K&1];t=(t&~(1<<K))|(a.w<<K);if(a.d==1){int v=t>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=t<<1&MASK;add(a.n,v);add(a.n,v|1);}}
 vector<array<vector<Case>,2>>cases(S);for(q=0;q<S;q++)for(int t=0;t<N;t++)if(seen[q][t]){Case cs{t,{}};C x{q,0,t};for(int k=1;k<=L;k++){if(x.h<-K||x.h>K||x.q>=S)break;auto a=rows[x.q][x.t>>(x.h+K)&1];x.t=(x.t&~(1<<(x.h+K)))|(a.w<<(x.h+K));x.h+=a.d;x.q=a.n;cs.goals.push_back(x);}cases[q][t>>K&1].push_back(cs);}
 long long tried=0,passes=0;
 for(q=0;q<S;q++)for(b=0;b<2;b++)for(n=0;n<=S;n++)for(w=0;w<2;w++)for(int d:{-1,1}){A patch{w,d,n},old=rows[q][b];if(patch.w==old.w&&patch.d==old.d&&patch.n==old.n)continue;tried++;bool good=true;int maxnew=0,maxold=0;
  for(const auto&cs:cases[q][b]){C y{q,0,cs.t};bool hit=false;for(int k=1;k<=M;k++){if(y.h<-K||y.h>K||y.q>=S)break;int bit=y.t>>(y.h+K)&1;A a=(y.q==q&&bit==b)?patch:rows[y.q][bit];y.t=(y.t&~(1<<(y.h+K)))|(a.w<<(y.h+K));y.h+=a.d;y.q=a.n;for(int j=0;j<(int)cs.goals.size();j++)if(eq(y,cs.goals[j])){hit=true;maxnew=max(maxnew,k);maxold=max(maxold,j+1);break;}if(hit)break;}if(!hit){good=false;break;}}
  if(good){passes++;cout<<"{\"state\":"<<q<<",\"read\":"<<b<<",\"patch\":["<<w<<','<<d<<','<<n<<"],\"contexts\":"<<cases[q][b].size()<<",\"max_new_steps\":"<<maxnew<<",\"max_old_steps\":"<<maxold<<"}"<<endl;}}
 cerr<<"tried="<<tried<<" passes="<<passes<<" radius="<<K<<" old_bound="<<L<<" new_bound="<<M<<endl;
}
