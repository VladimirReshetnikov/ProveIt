// Pair quotient search with jointly synthesized rows and a changed arrival bit.
// Positive cases require explicit universal rechecking; negative cases are bounded.
#include <bits/stdc++.h>
using namespace std;struct A{int w,d,n;};struct C{int q,h,t;};struct Test{int oldq,p,h,t;bool ready=false;unordered_set<long long>targets;};
int main(int argc,char**argv){if(argc<4)return 2;int K=stoi(argv[2]),DEPTH=stoi(argv[3]),N=1<<(2*K+1),MASK=N-1;map<int,array<A,2>>r;vector<int>states;int q,b,w,n;char d;string line;ifstream in(argv[1]);while(getline(in,line)){istringstream s(line);if(s>>q>>b>>w>>d>>n)r[q][b]={w,d=='R'?1:-1,n};}for(auto const&x:r)states.push_back(x.first);
 map<int,vector<int>>pats;if(argc>4&&string(argv[4])!="-"){ifstream pin(argv[4]);int p;while(pin>>q>>p)pats[q].push_back(p);}else{map<int,vector<bool>>seen;queue<pair<int,int>>todo;for(int q:states)seen[q]=vector<bool>(N);auto add=[&](int q,int p){if(!r.count(q)||seen[q][p])return;seen[q][p]=true;todo.emplace(q,p);};add(74,0);while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=r[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(2*K)));}else{int v=p<<1&MASK;add(a.n,v);add(a.n,v|1);}}for(int q:states)for(int p=0;p<N;p++)if(seen[q][p])pats[q].push_back(p);}
 for(int q:states)if(pats[q].empty()){cerr<<"Missing contexts "<<q<<endl;return 3;}
 auto key=[&](int q,int h,int t){return((static_cast<long long>(q)*64+h+K+4)*N+t);};
 unordered_map<long long,vector<C>>tracecache;
 auto trace=[&](int q,int p)->vector<C>&{long long ky=static_cast<long long>(q)*N+p;auto it=tracecache.find(ky);if(it!=tracecache.end())return it->second;vector<C>v;unordered_set<long long>seen;int h=0,t=p;for(int st=0;st<DEPTH;st++){if(!r.count(q)||h<-K||h>K)break;A a=r[q][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(a.w<<(h+K));h+=a.d;q=a.n;auto sk=key(q,h,t);if(seen.count(sk))break;seen.insert(sk);v.push_back({q,h,t});}return tracecache.emplace(ky,move(v)).first->second;};
 long long pairs=0,trials=0,solutions=0;
 for(int a:states){if(a==74)continue;set<int>dirs;for(auto const&[q,acts]:r)if(q!=a)for(auto x:acts)if(x.n==a)dirs.insert(x.d);int dir=dirs.size()==1?*dirs.begin():0;vector<pair<int,int>>rels={{0,0}};if(dir){rels.push_back({0,1});rels.push_back({-2*dir,0});rels.push_back({-2*dir,1});}
  for(auto[shift,toggle]:rels)for(int keep:states){if(keep==a)continue;pairs++;array<A,2>win;bool pairgood=true;
   for(int bit:{0,1}){vector<Test>tests;for(int p:pats[keep])if((p>>K&1)==bit)tests.push_back({keep,p,0,p});for(int p:pats[a]){int t=p^(toggle?1<<(K-dir):0);if((t>>(K+shift)&1)==bit)tests.push_back({a,p,shift,t});}
    // Interleave the two origins so most impossible actions fail promptly.
    stable_sort(tests.begin(),tests.end(),[&](auto const&x,auto const&y){return (x.p*2+(x.oldq==a))<(y.p*2+(y.oldq==a));});
    bool found=false;for(int target:states){if(target==a)continue;for(int wr:{0,1})for(int move:{-1,1}){trials++;A first{wr,move,target};bool good=true;
     for(auto &tc:tests){if(!tc.ready){for(C oc:trace(tc.oldq,tc.p)){if(oc.q==a&&toggle&&(oc.h-dir<-K||oc.h-dir>K))continue;int tt=oc.t^((oc.q==a&&toggle)?1<<(oc.h-dir+K):0);tc.targets.insert(key(oc.q==a?keep:oc.q,oc.h+(oc.q==a?shift:0),tt));}tc.ready=true;}
      int h=tc.h,t=(tc.t&~(1<<(h+K)))|(wr<<(h+K)),q=target;h+=move;bool hit=false;
      for(int st=1;st<=DEPTH;st++){if(tc.targets.count(key(q,h,t))){hit=true;break;}if(q==keep||!r.count(q)||h<-K||h>K)break;A x=r[q][t>>(h+K)&1];bool dst=x.n==a;int nw=x.w^(dst?toggle:0);t=(t&~(1<<(h+K)))|(nw<<(h+K));h+=x.d+(dst?shift:0);q=dst?keep:x.n;}
      if(!hit){good=false;break;}
     }
     if(good){found=true;win[bit]=first;break;}
    }if(found)break;}
    if(!found){pairgood=false;break;}
   }
   if(pairgood){solutions++;cout<<"{\"remove\":"<<a<<",\"keep\":"<<keep<<",\"shift\":"<<shift<<",\"toggle\":"<<toggle<<",\"arrival_direction\":"<<dir<<",\"actions\":[["<<win[0].w<<','<<win[0].d<<','<<win[0].n<<"],["<<win[1].w<<','<<win[1].d<<','<<win[1].n<<"]]}"<<endl;}
  }
  cerr<<"Finished remove "<<a<<" pairs "<<pairs<<" trials "<<trials<<" solutions "<<solutions<<endl;
 }
 cerr<<"SUMMARY pairs "<<pairs<<" first_actions "<<trials<<" solutions "<<solutions<<endl;
}
