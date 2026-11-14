// Search one-row positive-progress neutral transformations on a finite envelope.
// A returned row needs its own standalone closure and source-binding proof.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
int main(int argc,char**argv){
 if(argc<4)return 2;int K=stoi(argv[2]),B=stoi(argv[3]),N=1<<(2*K+1),M=N-1;
 array<A,2>row[3000];bool ex[3000]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;row[q][b]={w,d=='R'?1:-1,n};}
 map<int,vector<bool>>seen;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(q<0||q>=3000||!ex[q])return;if(!seen.count(q))seen[q]=vector<bool>(N);if(!seen[q][p])seen[q][p]=1,todo.emplace(q,p);};
 add(74,0);while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=row[q][p>>K&1];p=(p&~(1<<K))|a.w<<K;if(a.d==1){add(a.n,p>>1);add(a.n,(p>>1)|(1<<2*K));}else{add(a.n,(p<<1)&M);add(a.n,((p<<1)&M)|1);}}
 vector<int>pat[3000][2];for(int q:qs)for(int p=0;p<N;p++)if(seen[q][p])pat[q][p>>K&1].push_back(p);
 if(argc>4){ifstream ps(argv[4]);map<int,vector<int>>custom;int p;while(ps>>q>>p)custom[q].push_back(p);for(auto&[q,pp]:custom){pat[q][0].clear();pat[q][1].clear();for(int p:pp)pat[q][p>>K&1].push_back(p);}}
 for(int q:qs)for(int b:{0,1}){A old=row[q][b];for(int n:qs)for(int w:{0,1})for(int d:{-1,1}){A a{w,d,n};if(a==old)continue;bool ok=true;int maxst=0;
  for(int p:pat[q][b]){int tq=old.n,th=old.d,tt=(p&~(1<<K))|(old.w<<K),cq=a.n,h=a.d,t=(p&~(1<<K))|(a.w<<K);bool hit=false;
   for(int st=1;st<=B;st++){if(cq==tq&&h==th&&t==tt){hit=true;maxst=max(maxst,st);break;}if(h<-K||h>K||cq<0||cq>=3000||!ex[cq]||cq==q)break;A aa=row[cq][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(aa.w<<(h+K));h+=aa.d;cq=aa.n;}
   if(!hit){ok=false;break;}
  }
  if(ok)cout<<"{\"state\":"<<q<<",\"read\":"<<b<<",\"old\":["<<old.w<<","<<old.d<<","<<old.n<<"],\"new\":["<<a.w<<","<<a.d<<","<<a.n<<"],\"max_steps\":"<<maxst<<"}"<<endl;
 }}
}
