#include <cstdint>
#include <array>
#include <vector>
#include <queue>
#include <unordered_set>
#include <fstream>
#include <iostream>
#include <sstream>
#include <cstdlib>
using namespace std;
struct Row {int w,d,n;};
struct C {int q,h,t;};
int main(int argc,char**argv){
 if(argc<2)return 2; const int K=argc>2?atoi(argv[2]):4,L=argc>3?atoi(argv[3]):32,M=argc>4?atoi(argv[4]):64;
 const int W=2*K+1,N=1<<W,MASK=N-1; int S=0,q,b,w,n;char d;string line; vector<array<Row,2>> rows(5000);vector<bool>present(5000);
 ifstream in(argv[1]);while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};present[q]=true;S=max(S,q+1);}
 if(S>1000)return 3; for(int q=0;q<S;q++)if(!present[q])return 4;
 vector<vector<bool>>seen(S,vector<bool>(N));queue<pair<int,int>>todo;auto add=[&](int q,int t){if(q<S&&!seen[q][t]){seen[q][t]=true;todo.emplace(q,t);}};add(0,0);
 while(!todo.empty()){auto[q,t]=todo.front();todo.pop();auto a=rows[q][t>>K&1];t=(t&~(1<<K))|(a.w<<K);if(a.d==1){int v=t>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=t<<1&MASK;add(a.n,v);add(a.n,v|1);}}
 vector<vector<int>> pats(S);size_t count=0;for(int q=0;q<S;q++)for(int t=0;t<N;t++)if(seen[q][t]){pats[q].push_back(t);count++;}
 int matches=0,checked=0;auto key=[&](C c){return ((uint64_t)c.t<<20)|((uint64_t)(c.h+K)<<12)|c.q;};
 for(int a=0;a<S;a++)for(int r=0;r<S;r++)if(a!=r){checked++;bool okay=true;int longest=0,maxorig=0;
  for(int t:pats[a]){vector<C>targets;C x{a,0,t};for(int k=1;k<=L;k++){if(x.h<-K||x.h>K||x.q>=S)break;auto op=rows[x.q][x.t>>(x.h+K)&1];x.t=(x.t&~(1<<(x.h+K)))|(op.w<<(x.h+K));x.h+=op.d;x.q=op.n;C g=x;if(g.q==a)g.q=r;targets.push_back(g);}
    C y{r,0,t};bool hit=false;for(int k=1;k<=M;k++){if(y.h<-K||y.h>K||y.q>=S)break;auto op=rows[y.q][y.t>>(y.h+K)&1];y.t=(y.t&~(1<<(y.h+K)))|(op.w<<(y.h+K));y.h+=op.d;y.q=op.n==a?r:op.n;
     for(int j=0;j<(int)targets.size();j++)if(targets[j].q==y.q&&targets[j].h==y.h&&targets[j].t==y.t){hit=true;longest=max(longest,k);maxorig=max(maxorig,j+1);break;}if(hit)break;
    }if(!hit){okay=false;break;}
  }if(okay){matches++;cout<<"{\"drop\":"<<a<<",\"keep\":"<<r<<",\"contexts\":"<<pats[a].size()<<",\"max_new_steps\":"<<longest<<",\"max_old_steps\":"<<maxorig<<"}"<<endl;}
 }
 cerr<<"states="<<S<<" abstract_contexts="<<count<<" radius="<<K<<" original_bound="<<L<<" candidate_bound="<<M<<" pairs="<<checked<<" survivors="<<matches<<endl;
}
