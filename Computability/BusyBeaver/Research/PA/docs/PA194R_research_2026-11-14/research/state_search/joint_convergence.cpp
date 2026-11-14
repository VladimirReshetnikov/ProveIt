// Synthesize a two-row quotient, allowing repeated visits to its new control.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;}; struct Test{int old,p,b;};
int main(int argc,char**argv){
 if(argc<4)return 2;int K=stoi(argv[2]),BOUND=stoi(argv[3]),N=1<<(2*K+1),MASK=N-1;
 array<A,2> rows[3000];bool exists[3000]={};vector<int>states;ifstream in(argv[1]);string line;int q,b,w,n;char dr;
 while(getline(in,line)){istringstream s(line);if(!(s>>q>>b>>w>>dr>>n))continue;if(!exists[q])states.push_back(q);exists[q]=true;rows[q][b]={w,dr=='R'?1:-1,n};}
 map<int,vector<bool>>seen;queue<pair<int,int>>todo;auto add=[&](int q,int p){if(q<0||q>=3000||!exists[q])return;if(!seen.count(q))seen[q]=vector<bool>(N);if(!seen[q][p]){seen[q][p]=true;todo.emplace(q,p);}};
 add(74,0);while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(2*K)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 vector<int>pat[3000];for(int q:states)for(int p=0;p<N;p++)if(seen[q][p])pat[q].push_back(p);
 if(argc>4){ifstream ps(argv[4]);map<int,vector<int>>custom;int p;while(ps>>q>>p)custom[q].push_back(p);for(auto&[q,ps]:custom)pat[q]=ps;}
 auto encode=[&](int q,int h,int t){return (static_cast<uint64_t>(q)*(2*K+3)+h+K+1)*N+t;};
 unordered_map<uint64_t,unordered_set<uint64_t>> targets;
 for(int oldq:states)for(int p:pat[oldq]){auto&out=targets[static_cast<uint64_t>(oldq)*N+p];int q=oldq,h=0,t=p;for(int st=0;st<BOUND;st++){if(q<0||q>=3000||!exists[q]||h<-K||h>K)break;A op=rows[q][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;q=op.n;auto k=encode(q,h,t);if(!out.insert(k).second)break;}}
 long long pairs=0,trials=0,combos=0,hits=0;auto started=chrono::steady_clock::now();
 for(int a:states){for(int keep:states){if(a>=keep)continue;pairs++;vector<Test> tests[2];for(int q:{a,keep})for(int p:pat[q])tests[p>>K&1].push_back({q,p,p>>K&1});for(int b:{0,1})sort(tests[b].begin(),tests[b].end(),[](auto&x,auto&y){return x.p<y.p||(x.p==y.p&&x.old<y.old);});
  vector<A> choices[2];array<A,2> acts;int known;
  auto check=[&](const Test&tc)->int{
   A old=rows[tc.old][tc.b];int tq=old.n==a?keep:old.n,th=old.d,tt=(tc.p&~(1<<K))|(old.w<<K);
   int q=keep,h=0,t=tc.p;
   for(int st=0;st<=BOUND;st++){
    if(st){auto&ts=targets[static_cast<uint64_t>(tc.old)*N+tc.p];if(ts.count(encode(q,h,t))||(q==keep&&ts.count(encode(a,h,t))))return 1;}
    if(st==BOUND||h<-K||h>K||q<0||q>=3000||!exists[q])return 0;
    int bit=t>>(h+K)&1;A op;
    if(q==keep){if(!(known>>bit&1))return 2;op=acts[bit];}else op=rows[q][bit];
    t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;q=op.n==a?keep:op.n;
   }return 0;
  };
  bool possible=true;
  vector<int>destinations=states;destinations.push_back(254);for(int bit:{0,1}){known=1<<bit;for(int target:destinations){if(target==a)continue;for(int wr:{0,1})for(int dir:{-1,1}){trials++;acts[bit]={wr,dir,target};bool ok=true;for(auto&tc:tests[bit])if(!check(tc)){ok=false;break;}if(ok)choices[bit].push_back(acts[bit]);}}
   if(choices[bit].empty()){possible=false;break;}
  }
  if(!possible)continue;
  known=3;for(A z:choices[0])for(A o:choices[1]){combos++;acts={z,o};bool ok=true;for(int bit:{0,1}){for(auto&tc:tests[bit])if(check(tc)!=1){ok=false;break;}if(!ok)break;}
   if(ok){hits++;cout<<"{\"remove\":"<<a<<",\"keep\":"<<keep<<",\"actions\":[["<<z.w<<','<<z.d<<','<<z.n<<"],["<<o.w<<','<<o.d<<','<<o.n<<"]]}"<<endl;}
  }
 }cerr<<"Q "<<a<<" pairs "<<pairs<<" trials "<<trials<<" combos "<<combos<<" hits "<<hits<<endl;}
 cerr<<"DONE pairs "<<pairs<<" trials "<<trials<<" combos "<<combos<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}
