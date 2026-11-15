// One-row, two-sided positive-progress stuttering synthesis.
#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
struct C {int q,h,t;};
int main(int argc,char**argv){
 if(argc<6)return 2;int K=stoi(argv[2]),OLD=stoi(argv[3]),B=stoi(argv[4]),START=stoi(argv[5]),N=1<<(2*K+1),M=N-1;
 array<A,2>row[4096];bool ex[4096]={};vector<int>qs;ifstream f(argv[1]);string line;int q,b,w,n;char d;
 while(getline(f,line)){istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;if(!ex[q])qs.push_back(q);ex[q]=true;row[q][b]={w,d=='R'?1:-1,n};}
 vector<vector<bool>>seen(4096);queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(!ex[q])return;if(seen[q].empty())seen[q].resize(N);if(!seen[q][p])seen[q][p]=true,todo.emplace(q,p);};
 add(START,0);while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=row[q][p>>K&1];p=(p&~(1<<K))|a.w<<K;if(a.d==1){add(a.n,p>>1);add(a.n,(p>>1)|(1<<2*K));}else{add(a.n,(p<<1)&M);add(a.n,((p<<1)&M)|1);}}
 vector<int>pat[4096][2];for(int q:qs)for(int p=0;p<N;p++)if(!seen[q].empty()&&seen[q][p])pat[q][p>>K&1].push_back(p);
 if(argc>6){ifstream ps(argv[6]);map<int,vector<int>>custom;int p;while(ps>>q>>p)custom[q].push_back(p);for(auto&[q,pp]:custom){pat[q][0].clear();pat[q][1].clear();for(int p:pp)pat[q][p>>K&1].push_back(p);}}
 vector<int>targets=qs;for(int q:qs)for(int b:{0,1})if(!ex[row[q][b].n]&&find(targets.begin(),targets.end(),row[q][b].n)==targets.end())targets.push_back(row[q][b].n);
 for(int q:qs)for(int b:{0,1}){A old=row[q][b];vector<vector<C>>orbits;
  for(int p:pat[q][b]){C c{q,0,p};vector<C>orb;for(int s=0;s<OLD&&ex[c.q]&&abs(c.h)<=K;s++){A a=row[c.q][c.t>>(K+c.h)&1];c.t=(c.t&~(1<<(K+c.h)))|(a.w<<(K+c.h));c.h+=a.d;c.q=a.n;orb.push_back(c);}orbits.push_back(move(orb));}
  for(int n:targets)for(int w:{0,1})for(int d:{-1,1}){A a{w,d,n};if(a==old)continue;bool ok=true;int maxnew=0,maxold=0;
   for(size_t i=0;i<orbits.size();i++){int p=pat[q][b][i];C c{q,0,p};bool hit=false;
    for(int st=0;st<=B;st++){
     if(st)for(int j=0;j<(int)orbits[i].size();j++){C ref=orbits[i][j];if(c.q==ref.q&&c.h==ref.h&&c.t==ref.t){hit=true;maxnew=max(maxnew,st);maxold=max(maxold,j+1);break;}}
     if(hit||st==B||abs(c.h)>K||!ex[c.q])break;
     int bit=c.t>>(K+c.h)&1;A act=(c.q==q&&bit==b)?a:row[c.q][bit];c.t=(c.t&~(1<<(K+c.h)))|(act.w<<(K+c.h));c.h+=act.d;c.q=act.n;
    }
    if(!hit){ok=false;break;}
   }
   if(ok)cout<<"{\"state\":"<<q<<",\"read\":"<<b<<",\"old\":["<<old.w<<','<<old.d<<','<<old.n<<"],\"new\":["<<a.w<<','<<a.d<<','<<a.n<<"],\"max_new_steps\":"<<maxnew<<",\"max_old_steps\":"<<maxold<<"}"<<endl;
  }
 }
}
