// Search control elimination by rewriting incoming transitions.
// Original and replacement trajectories must meet, with exact local tape/head,
// at an unchanged transition (neither q nor an incoming row being rewritten).
// Contexts overapproximate source runs. Discovery only: symbolic/startup proof
// must validate a whole candidate. New search code; see the enclosing repository license.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};
struct C{int q,h,t;};
int main(int argc,char**argv){
 if(argc<5)return 2;
 int K=stoi(argv[2]),BOUND=stoi(argv[3]),N=1<<(2*K+1),MASK=N-1;
 array<A,2> rows[4000];bool exists[4000]={};vector<int>states;
 ifstream in(argv[1]);string line;int q,b,w,n;char dr;
 while(getline(in,line)){istringstream s(line);if(!(s>>q>>b>>w>>dr>>n))continue;if(!exists[q])states.push_back(q);exists[q]=true;rows[q][b]={w,dr=='R'?1:-1,n};}
 map<int,vector<bool>>seen;queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(q<0||q>=4000||!exists[q])return;if(!seen.count(q))seen[q]=vector<bool>(N);if(!seen[q][p]){seen[q][p]=true;todo.emplace(q,p);}};
 add(74,0);while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(2*K)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 vector<int>pat[4000];for(int q:states)if(seen.count(q))for(int p=0;p<N;p++)if(seen[q][p])pat[q].push_back(p);
 {ifstream ps(argv[4]);map<int,vector<int>>custom;int p;while(ps>>q>>p)custom[q].push_back(p);for(auto&[q,ps]:custom)pat[q]=ps;}
 long long controls=0,edges=0,trials=0,hits=0;auto started=chrono::steady_clock::now();
 for(int removed:states){
   if(removed==74)continue;
   vector<pair<int,int>> incoming;for(int u:states)if(u!=removed)for(int bit:{0,1})if(rows[u][bit].n==removed)incoming.push_back({u,bit});
   if(incoming.empty())continue;
   controls++;vector<vector<A>> choices;bool possible=true;
   // Exact old-path checkpoints for each input window; original paths may use removed.
   for(auto [u,bit]:incoming){
     edges++;vector<int>inputs;vector<vector<C>> oldPaths;
     for(int p:pat[u])if((p>>K&1)==bit){
       vector<C>path;C c={u,0,p};
       for(int st=0;st<BOUND;++st){
         if(c.h<-K||c.h>K||!exists[c.q])break;
         int bv=c.t>>(c.h+K)&1;A a=rows[c.q][bv];c.t=(c.t&~(1<<(c.h+K)))|(a.w<<(c.h+K));c.h+=a.d;c.q=a.n;
         if(c.h<-K||c.h>K||!exists[c.q])break;
         // Stop checkpoint expansion once another rewritten incoming row is reached.
         int nb=c.t>>(c.h+K)&1;
         if(c.q!=removed&&rows[c.q][nb].n!=removed)path.push_back(c);
         if(c.q!=removed&&rows[c.q][nb].n==removed)break;
       }
       if(path.empty()){possible=false;break;}
       inputs.push_back(p);oldPaths.push_back(move(path));
     }
     if(!possible)break;
     vector<A>good;
     for(int target:states)if(target!=removed)for(int wr:{0,1})for(int dir:{-1,1}){
       trials++;A cand={wr,dir,target};bool ok=true;
       for(int i=0;i<(int)inputs.size();++i){
         C c={target,dir,(inputs[i]&~(1<<K))|(wr<<K)};bool match=false;
         for(int st=1;st<=BOUND;++st){
           if(c.q==removed||c.h<-K||c.h>K||!exists[c.q])break;
           for(C oc:oldPaths[i])if(c.q==oc.q&&c.h==oc.h&&c.t==oc.t){match=true;break;}
           if(match)break;
           int bv=c.t>>(c.h+K)&1;
           if(rows[c.q][bv].n==removed)break;
           A a=rows[c.q][bv];c.t=(c.t&~(1<<(c.h+K)))|(a.w<<(c.h+K));c.h+=a.d;c.q=a.n;
         }
         if(!match){ok=false;break;}
       }
       if(ok)good.push_back(cand);
     }
     if(good.empty()){possible=false;break;}choices.push_back(good);
   }
   if(possible){hits++;cout<<"{\"remove\":"<<removed<<",\"incoming\":[";
     for(int i=0;i<(int)incoming.size();++i){if(i)cout<<',';cout<<"{\"row\":["<<incoming[i].first<<','<<incoming[i].second<<"],\"choices\":[";for(int j=0;j<(int)choices[i].size();++j){if(j)cout<<',';A a=choices[i][j];cout<<'['<<a.w<<','<<a.d<<','<<a.n<<']';}cout<<"]}"; }cout<<"]}"<<endl;
   }
   cerr<<"Q "<<removed<<" controls "<<controls<<" edges "<<edges<<" trials "<<trials<<" hits "<<hits<<endl;
 }
 cerr<<"DONE controls "<<controls<<" edges "<<edges<<" trials "<<trials<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}
