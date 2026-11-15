#include <array>
#include <vector>
#include <queue>
#include <fstream>
#include <iostream>
#include <sstream>
#include <cstdlib>
#include <cstdint>
using namespace std;
struct Row{int w,d,n;};struct C{int q,h,t;};struct Case{int q,t;vector<C> goals;};
vector<array<Row,2>> rows(5000);int S,K,L,M;uint64_t checks=0;Row patches[2];bool known[2];
bool equal(C a,C b){return a.q==b.q&&a.h==b.h&&a.t==b.t;}
int trial(int drop,int keep,const Case& cs){checks++;C y{keep,0,cs.t};for(int k=1;k<=M;k++){
 if(y.h<-K||y.h>K||y.q>=S)return 0;int b=y.t>>(y.h+K)&1;Row op;
 if(y.q==keep){if(!known[b])return 2;op=patches[b];}else op=rows[y.q][b];
 y.t=(y.t&~(1<<(y.h+K)))|(op.w<<(y.h+K));y.h+=op.d;y.q=op.n==drop?keep:op.n;
 for(auto g:cs.goals){if(g.q==drop)g.q=keep;if(equal(g,y))return 1;}
 }return 0;}
int main(int argc,char**argv){if(argc<2)return 2;K=argc>2?atoi(argv[2]):4;L=argc>3?atoi(argv[3]):4;M=argc>4?atoi(argv[4]):16;int W=2*K+1,N=1<<W,MASK=N-1;int q,b,w,n;char d;string line;vector<bool>pres(5000);
 ifstream in(argv[1]);while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};pres[q]=true;S=max(S,q+1);}for(q=0;q<S;q++)if(!pres[q])return 3;
 vector<vector<bool>>seen(S,vector<bool>(N));queue<pair<int,int>>todo;auto add=[&](int q,int t){if(q<S&&!seen[q][t]){seen[q][t]=true;todo.emplace(q,t);}};add(0,0);
 while(!todo.empty()){auto[q,t]=todo.front();todo.pop();auto a=rows[q][t>>K&1];t=(t&~(1<<K))|(a.w<<K);if(a.d==1){int v=t>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=t<<1&MASK;add(a.n,v);add(a.n,v|1);}}
 vector<array<vector<Case>,2>>cases(S);size_t count=0;for(q=0;q<S;q++)for(int t=0;t<N;t++)if(seen[q][t]){Case cs{q,t,{}};C x{q,0,t};for(int k=1;k<=L;k++){if(x.h<-K||x.h>K||x.q>=S)break;auto op=rows[x.q][x.t>>(x.h+K)&1];x.t=(x.t&~(1<<(x.h+K)))|(op.w<<(x.h+K));x.h+=op.d;x.q=op.n;cs.goals.push_back(x);}cases[q][t>>K&1].push_back(cs);count++;}
 uint64_t pairs=0,actiontrials=0,fullpairs=0;int solutions=0;
 for(int drop=0;drop<S;drop++)for(int keep=drop+1;keep<S;keep++){pairs++;array<vector<Row>,2> opts;bool failed=false;
  for(int bit=0;bit<2;bit++){known[bit]=true;known[1-bit]=false;
   for(int dest=0;dest<=S;dest++)if(dest!=drop)for(int w=0;w<2;w++)for(int d:{-1,1}){Row a{w,d,dest};patches[bit]=a;actiontrials++;bool good=true;
    for(int src:{drop,keep}){for(const auto&cs:cases[src][bit])if(!trial(drop,keep,cs)){good=false;break;}if(!good)break;}if(good)opts[bit].push_back(a);
   }if(opts[bit].empty()){failed=true;break;}
  }if(failed)continue;known[0]=known[1]=true;
  for(auto a:opts[0])for(auto b:opts[1]){patches[0]=a;patches[1]=b;fullpairs++;bool good=true;
   for(int src:{drop,keep}){for(int bit=0;bit<2;bit++){for(const auto&cs:cases[src][bit])if(trial(drop,keep,cs)!=1){good=false;break;}if(!good)break;}if(!good)break;}
   if(good){solutions++;cout<<"{\"drop\":"<<drop<<",\"keep\":"<<keep<<",\"rows\":[["<<a.w<<','<<a.d<<','<<a.n<<"],["<<b.w<<','<<b.d<<','<<b.n<<"]]}"<<endl;}
  }
 }
 cerr<<"states="<<S<<" contexts="<<count<<" radius="<<K<<" original_bound="<<L<<" candidate_bound="<<M<<" unordered_pairs="<<pairs<<" actiontrials="<<actiontrials<<" full_row_pairs="<<fullpairs<<" cases_checked="<<checks<<" survivors="<<solutions<<endl;
}
