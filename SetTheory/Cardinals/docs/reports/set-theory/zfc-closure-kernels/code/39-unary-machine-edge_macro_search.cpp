#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <tuple>
#include <vector>
using namespace std;
struct A {int w,d,t;};
struct C {int q,h; uint64_t tape;bool operator==(const C&o)const{return q==o.q&&h==o.h&&tape==o.tape;}};
int RAD,N,FUEL=64;array<array<A,2>,255>T;set<int>prot;
map<pair<int,int>,vector<uint64_t>> pats;
vector<C> trajectory(int q,uint64_t pat,int removed,bool candidate){
 vector<C> out;int h=RAD;
 for(int k=0;k<FUEL;k++){
  if(q==254||h<0||h>2*RAD||(candidate&&q==removed))break;
  A a=T[q][(pat>>h)&1];
  if(a.w)pat|=1ULL<<h;else pat&=~(1ULL<<h);
  h+=a.d;q=a.t;
  if(q==8)break;
  out.push_back({q,h,pat});
 }
 return out;
}
bool match(int p,int q,uint64_t pat){
 auto a=trajectory(p,pat,p,false),b=trajectory(q,pat,p,true);
 for(auto x:a){if(x.q==p)continue;for(auto y:b)
  if((x.q==254&&y.q==254)||x==y)return true;}
 return false;
}
int main(int argc,char**argv){
 if(argc<2)return 1;if(argc>2)FUEL=stoi(argv[2]);ifstream in(argv[1]);
 int k,m;in>>RAD>>N>>k>>m;
 if(!in||RAD<1||RAD>20||N!=254||FUEL<1||k<0||k>255||m<0||m>508){cerr<<"invalid input header\n";return 2;}
 for(int i=0,x;i<k;i++){in>>x;prot.insert(x);}
 for(int q=0;q<N;q++)for(int b=0;b<2;b++)in>>T[q][b].w>>T[q][b].d>>T[q][b].t;
 for(int j=0;j<m;j++){int q,b,n;in>>q>>b>>n;auto &v=pats[{q,b}];for(int i=0;i<n;i++){uint64_t a;in>>a;v.push_back(a);}}
 if(!in){cerr<<"truncated input\n";return 2;}
 for(int q=0;q<N;q++)if(q!=8)for(int b=0;b<2;b++){auto a=T[q][b];if(a.w<0||a.w>1||(a.d!=-1&&a.d!=1)||a.t<0||a.t>254||a.t==8){cerr<<"invalid transition\n";return 2;}}
 for(auto [e,ps]:pats){if(e.first<0||e.first>=N||e.first==8||e.second<0||e.second>1){cerr<<"invalid edge\n";return 2;}for(auto p:ps)if(p>=(1ULL<<(2*RAD+1))){cerr<<"invalid pattern\n";return 2;}}
 int eligible=0,edgechecks=0,pairchecks=0,patternchecks=0,totaledgeopts=0,totalpossible=0;
 cout<<"radius "<<RAD<<" fuel "<<FUEL<<"\n";
 for(int p=0;p<N;p++){
  if(p==8||prot.count(p)||T[p][0].t==p||T[p][1].t==p)continue;
  eligible++;bool possible=true;vector<tuple<int,int,vector<int>>> results;
  for(int r=0;r<N;r++)if(r!=8)for(int b=0;b<2;b++)if(T[r][b].t==p){
   auto it=pats.find({r,b});vector<int>opts;edgechecks++;
   if(it!=pats.end()&&!it->second.empty()){
    for(int q=0;q<N;q++)if(q!=8&&q!=p){
     pairchecks++;bool ok=true;
     for(auto pattern:it->second){patternchecks++;if(!match(p,q,pattern)){ok=false;break;}}
     if(ok)opts.push_back(q);
    }
   }
   if(opts.empty())possible=false;totaledgeopts+=opts.size();
   results.push_back({r,b,opts});
  }
  cout<<"state "<<p<<" possible "<<possible<<"\n";
  for(auto [r,b,opts]:results){
   cout<<"edge "<<r<<" "<<b<<" "<<p<<" patterns "<<pats[{r,b}].size()<<" choices";
   for(int q:opts)cout<<" "<<q;
   cout<<"\n";
  }
  if(possible)totalpossible++;
 }
 cout<<"SUMMARY eligible "<<eligible<<" edges "<<edgechecks<<" target_checks "<<pairchecks<<" pattern_checks "<<patternchecks<<" option_count "<<totaledgeopts<<" possible "<<totalpossible<<"\n";
}
