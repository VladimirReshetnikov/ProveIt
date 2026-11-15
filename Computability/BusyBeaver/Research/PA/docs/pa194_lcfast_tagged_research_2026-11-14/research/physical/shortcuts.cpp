#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct A {int w,d,n;};
int main(int argc,char**argv){
 if(argc<2){cerr<<"usage: shortcuts TABLE [radius=6] [bound=101] [start=74]\n";return 2;}
 int R=argc>2?stoi(argv[2]):6,B=argc>3?stoi(argv[3]):101,START=argc>4?stoi(argv[4]):74;
 if(R>10||R<1)return 2;
 map<pair<int,int>,A> input;set<int> labels;ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,n;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&n);input[{q,b}]={w,d=='R'?1:-1,n};labels.insert(q);}
 vector<int> names(labels.begin(),labels.end());map<int,int> ix;int N=names.size();for(int i=0;i<N;i++)ix[names[i]]=i;
 vector<array<A,2>> tm(N);for(int i=0;i<N;i++)for(int b=0;b<2;b++){A a=input.at({names[i],b});a.n=ix.count(a.n)?ix[a.n]:N;tm[i][b]=a;}
 uint32_t W=2*R+1,K=1u<<W,mask=K-1,center=1u<<R;
 vector<uint8_t> seen((size_t)N*K,0);vector<uint32_t> queue;queue.reserve((size_t)N*K/4);
 auto add=[&](int q,uint32_t p){if(q==N)return;uint32_t code=q*K+p;if(!seen[code]){seen[code]=1;queue.push_back(code);}};
 add(ix.at(START),0);
 for(size_t j=0;j<queue.size();j++){uint32_t code=queue[j],p=code%K;int q=code/K;A a=tm[q][bool(p&center)];uint32_t v=(p&~center)|(a.w?center:0);if(a.d>0){v>>=1;add(a.n,v);add(a.n,v|(1u<<(2*R)));}else{v=(v<<1)&mask;add(a.n,v);add(a.n,v|1);}}
 cerr<<"REACHABLE_WINDOWS "<<queue.size()<<" RADIUS "<<R<<" BOUND "<<B<<"\n";
 if(argc>5){ifstream cf(argv[5]);int q;uint32_t p;set<int> reset;size_t records=0;while(cf>>q>>p){if(!ix.count(q)||p>=K)return 4;int s=ix[q];if(!reset.count(s)){fill(seen.begin()+(size_t)s*K,seen.begin()+(size_t)(s+1)*K,0);reset.insert(s);}seen[(size_t)s*K+p]=1;records++;}cerr<<"NARROWED_STATES "<<reset.size()<<" RECORDS "<<records<<"\n";}
 vector<array<vector<int>,2>> choices(N);int altered=0;
 for(int q=0;q<N;q++)for(int b=0;b<2;b++){
  vector<int> common;int count=0;
  for(uint32_t p=0;p<K;p++)if(bool(p&center)==b&&seen[(size_t)q*K+p]){
   vector<int> local;uint32_t t=p;int h=R,s=q;
   for(int step=1;step<=B;step++){
    if(s==N||h<0||h>=int(W))break;
    A a=tm[s][(t>>h)&1];t=(t&~(1u<<h))|(uint32_t(a.w)<<h);h+=a.d;s=a.n;
    if((h==R-1||h==R+1)&&((t^p)&~center)==0){
     int act=(((t>>R)&1)*2+(h==R+1))*(N+1)+s;
     local.push_back(act);
    }
   }
   sort(local.begin(),local.end());local.erase(unique(local.begin(),local.end()),local.end());
   if(count++==0)common=local;
   else{vector<int>x;set_intersection(common.begin(),common.end(),local.begin(),local.end(),back_inserter(x));common.swap(x);}
   if(common.size()==1){A old=tm[q][b];int act=(old.w*2+(old.d>0))*(N+1)+old.n;if(common[0]==act)break;}
  }
  choices[q][b]=common;A old=tm[q][b];int oldid=(old.w*2+(old.d>0))*(N+1)+old.n;
  if(common.size()>1){altered++;cout<<"ROW "<<names[q]<<" "<<b<<" PATTERNS_CHECKED "<<count<<" CHOICES";for(int v:common){int n=v%(N+1),wd=v/(N+1);cout<<" ["<<wd/2<<","<<(wd%2?'R':'L')<<","<<(n==N?-1:names[n])<<"]";}cout<<"\n";}
  if(count>0&&find(common.begin(),common.end(),oldid)==common.end()){cerr<<"BUG\n";return 3;}
 }
 int removable=0;
 for(int s=0;s<N;s++)if(names[s]!=START){bool ok=true;for(int q=0;q<N&&ok;q++)if(q!=s)for(int b=0;b<2;b++){bool good=choices[q][b].empty();for(int v:choices[q][b])if(v%(N+1)!=s)good=true;if(!good){ok=false;break;}}if(ok){removable++;cout<<"REMOVE "<<names[s]<<"\n";}}
 cerr<<"ALTERABLE_ROWS "<<altered<<" REMOVABLE "<<removable<<"\n";
}
