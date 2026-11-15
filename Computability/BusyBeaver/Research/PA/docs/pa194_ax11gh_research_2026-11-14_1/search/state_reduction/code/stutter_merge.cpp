// Two-sided positive-progress stuttering quotient synthesis.
// A hit is an exact bounded local certificate on an overapproximating
// reachable-window invariant. It is not a logical PA calibration.
#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;};
struct C {int q,h,t;};
struct Test {int old,p; vector<C> orbit;};
int main(int argc,char **argv) {
 if(argc<6) return 2;
 int K=stoi(argv[2]), OLD=stoi(argv[3]), B=stoi(argv[4]), START=stoi(argv[5]);
 int N=1<<(2*K+1), MASK=N-1;
 array<A,2> row[4096]; bool ex[4096]={}; vector<int> qs;
 ifstream in(argv[1]); string line; int q,b,w,n; char dr;
 while(getline(in,line)) {istringstream s(line); if(!(s>>q>>b>>w>>dr>>n))continue;
  if(!ex[q])qs.push_back(q); ex[q]=true; row[q][b]={w,dr=='R'?1:-1,n}; }
 vector<int> targets=qs; for(int q:qs)for(int b:{0,1})if(!ex[row[q][b].n]&&find(targets.begin(),targets.end(),row[q][b].n)==targets.end()) targets.push_back(row[q][b].n);
 vector<vector<bool>> seen(4096);queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!ex[q])return;if(seen[q].empty())seen[q].resize(N);if(!seen[q][p])seen[q][p]=true,todo.emplace(q,p);};
 add(START,0);
 while(!todo.empty()) {auto[q,p]=todo.front();todo.pop();A a=row[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
  if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(2*K)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 vector<int> pat[4096];for(int q:qs)for(int p=0;p<N;p++)if(!seen[q].empty()&&seen[q][p])pat[q].push_back(p);
 if(argc>6){ifstream ps(argv[6]);map<int,vector<int>>custom;int p;while(ps>>q>>p)custom[q].push_back(p);for(auto&[q,pp]:custom)pat[q]=pp;}
 vector<Test> tests[4096][2]; long long npat=0;
 for(int q:qs)for(int p:pat[q]) {Test x{q,p,{}}; C c{q,0,p};
  for(int step=0;step<OLD&&ex[c.q]&&abs(c.h)<=K;step++) {A a=row[c.q][c.t>>(K+c.h)&1]; c.t=(c.t&~(1<<(K+c.h)))|(a.w<<(K+c.h));c.h+=a.d;c.q=a.n;x.orbit.push_back(c);}
  tests[q][p>>K&1].push_back(move(x));npat++;}
 cerr<<"patterns "<<npat<<" K "<<K<<" old "<<OLD<<" new "<<B<<endl;
 long long pairs=0,trials=0,combos=0,hits=0;auto started=chrono::steady_clock::now();
 for(int q:qs)if(pat[q].empty())cerr<<"UNREACHABLE_CONTROL "<<q<<endl;
 for(int a:qs)for(int keep:qs) {if(a>=keep||pat[a].empty()||pat[keep].empty())continue;pairs++;
  vector<const Test*> ts[2];for(int b:{0,1})for(int q:{a,keep})for(auto&x:tests[q][b])ts[b].push_back(&x);
  for(int b:{0,1})sort(ts[b].begin(),ts[b].end(),[](auto x,auto y){return x->orbit.size()<y->orbit.size();});
  vector<A> choices[2];array<A,2> acts;int known;
  auto check=[&](const Test&tc)->int {
   int q=keep,h=0,t=tc.p;
   for(int step=0;step<=B;step++) {
    if(step)for(const C&old:tc.orbit)if(q==(old.q==a?keep:old.q)&&h==old.h&&t==old.t)return 1;
    if(step==B||abs(h)>K||!ex[q])return 0;
    int bit=t>>(h+K)&1;A op;
    if(q==keep){if(!(known>>bit&1))return 2;op=acts[bit];}else op=row[q][bit];
    t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;q=op.n==a?keep:op.n;
   }return 0;
  };
  bool possible=true;
  for(int bit:{0,1}){if(ts[bit].empty()){A op=row[keep][bit];if(op.n==a)op.n=keep;choices[bit].push_back(op);continue;}known=1<<bit;for(int target:targets){if(target==a)continue;for(int wr:{0,1})for(int dir:{-1,1}){trials++;acts[bit]={wr,dir,target};bool ok=true;for(auto x:ts[bit])if(!check(*x)){ok=false;break;}if(ok)choices[bit].push_back(acts[bit]);}}
   if(choices[bit].empty()){possible=false;break;}}
  if(!possible)continue;
  known=3;for(A z:choices[0])for(A o:choices[1]){combos++;acts={z,o};bool ok=true;for(int bit:{0,1}){for(auto x:ts[bit])if(check(*x)!=1){ok=false;break;}if(!ok)break;}
   if(ok){hits++;cout<<"{\"remove\":"<<a<<",\"keep\":"<<keep<<",\"actions\":[["<<z.w<<','<<z.d<<','<<z.n<<"],["<<o.w<<','<<o.d<<','<<o.n<<"]]}"<<endl;}}
  if(pairs%1000==0)cerr<<"pairs "<<pairs<<" trials "<<trials<<" combos "<<combos<<" hits "<<hits<<endl;
 }
 cerr<<"DONE pairs "<<pairs<<" trials "<<trials<<" combos "<<combos<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}
