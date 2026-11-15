#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct A{int w,d,n;};
int main(int argc,char**argv){
 if(argc<2)return 2;int R=argc>2?stoi(argv[2]):6,B=argc>3?stoi(argv[3]):100;
 map<pair<int,int>,A> inp;set<int> labels;ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,n;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&n);inp[{q,b}]={w,d=='R'?1:-1,n};labels.insert(q);}
 vector<int> names(labels.begin(),labels.end());map<int,int> ix;int N=names.size();for(int i=0;i<N;i++)ix[names[i]]=i;
 vector<array<A,2>> tm(N);vector<int> incoming(N,0);
 for(int i=0;i<N;i++)for(int b=0;b<2;b++){A a=inp.at({names[i],b});a.n=ix.count(a.n)?ix[a.n]:N;tm[i][b]=a;if(a.n<N)incoming[a.n]|=a.d<0?4:(1<<a.w);}
 vector<array<int,3>> pairs;
 for(int a=0;a<N;a++)if(incoming[a]==1&&names[a]!=74)for(int b=0;b<N;b++)if(incoming[b]==2&&names[b]!=74)for(int c=0;c<2;c++){
  A x=tm[a][c],y=tm[b][c];if(x.w==y.w&&x.d==y.d&&x.n==y.n)pairs.push_back({a,b,1-c});
 }
 cerr<<"PAIRS "<<pairs.size()<<"\n";for(auto p:pairs)cerr<<names[p[0]]<<" "<<names[p[1]]<<" divergent "<<p[2]<<"\n";
 uint32_t W=2*R+1,K=1u<<W,mask=K-1,center=1u<<R;
 vector<uint8_t> seen((size_t)N*K,0);vector<uint32_t> queue;queue.reserve((size_t)N*K/4);
 auto add=[&](int q,uint32_t p){if(q==N)return;uint32_t code=q*K+p;if(!seen[code]){seen[code]=1;queue.push_back(code);}};
 add(ix.at(74),0);
 for(size_t j=0;j<queue.size();j++){uint32_t code=queue[j],p=code%K;int q=code/K;A a=tm[q][bool(p&center)];uint32_t v=(p&~center)|(a.w?center:0);if(a.d>0){v>>=1;add(a.n,v);add(a.n,v|(1u<<(2*R)));}else{v=(v<<1)&mask;add(a.n,v);add(a.n,v|1);}}
 cerr<<"WINDOWS "<<queue.size()<<"\n";
 if(argc>4){ifstream cf(argv[4]);int q;uint32_t p;set<int> reset;size_t records=0;while(cf>>q>>p){if(!ix.count(q)||p>=K)return 4;int s=ix[q];if(!reset.count(s)){fill(seen.begin()+(size_t)s*K,seen.begin()+(size_t)(s+1)*K,0);reset.insert(s);}seen[(size_t)s*K+p]=1;records++;}cerr<<"NARROWED_STATES "<<reset.size()<<" RECORDS "<<records<<"\n";}
 // [q][original bit][tag] providers reaching the literal one-step endpoint.
 map<tuple<int,int,int>,vector<int>> providers;
 for(auto pair:pairs)for(int q:{pair[0],pair[1]})for(int tag=0;tag<2;tag++){
  int b=pair[2];auto key=make_tuple(q,b,tag);if(providers.count(key))continue;vector<int> us;
  for(int u=0;u<N;u++){
   bool all=true;int maxdur=0;
   for(uint32_t p=0;p<K&&all;p++)if(bool(p&center)==b&&seen[(size_t)q*K+p]){
    A old=tm[q][b];uint32_t goal=(p&~center)|(old.w?center:0),t=(p&~center)|(tag?center:0);int h=R,s=u;bool hit=false;
    for(int k=0;k<=B;k++){
     if(k>0&&h==R+old.d&&s==old.n&&t==goal){hit=true;maxdur=max(maxdur,k);break;}
     if(k==B||s==N||h<0||h>=int(W))break;A a=tm[s][(t>>h)&1];t=(t&~(1u<<h))|(uint32_t(a.w)<<h);h+=a.d;s=a.n;
    }
    if(!hit)all=false;
   }
   if(all)us.push_back(u);
  }
  providers[key]=us;cout<<"PROVIDERS "<<names[q]<<" BIT "<<b<<" TAG "<<tag<<":";for(int u:us)cout<<" "<<names[u];cout<<"\n";
 }
 int total=0;
 for(int i=0;i<(int)pairs.size();i++)for(int j=i+1;j<(int)pairs.size();j++){
  auto p=pairs[i],v=pairs[j];set<int> qs={p[0],p[1],v[0],v[1]};if(qs.size()!=4)continue;
  for(int tag=0;tag<2;tag++){
   vector<int>u,w;auto&x=providers[{p[0],p[2],tag}];auto&y=providers[{v[0],v[2],1-tag}];set_intersection(x.begin(),x.end(),y.begin(),y.end(),back_inserter(u));
   auto&a=providers[{p[1],p[2],tag}];auto&b=providers[{v[1],v[2],1-tag}];set_intersection(a.begin(),a.end(),b.begin(),b.end(),back_inserter(w));
   u.erase(remove_if(u.begin(),u.end(),[&](int q){return qs.count(q);}),u.end());w.erase(remove_if(w.begin(),w.end(),[&](int q){return qs.count(q);}),w.end());
   if(!u.empty()&&!w.empty()){total++;cout<<"NOMINATION "<<names[p[0]]<<" "<<names[p[1]]<<" "<<p[2]<<" "<<names[v[0]]<<" "<<names[v[1]]<<" "<<v[2]<<" TAG "<<tag<<" U";for(int q:u)cout<<" "<<names[q];cout<<" V";for(int q:w)cout<<" "<<names[q];cout<<"\n";}
  }
 }
 cerr<<"NOMINATIONS "<<total<<"\n";
}
