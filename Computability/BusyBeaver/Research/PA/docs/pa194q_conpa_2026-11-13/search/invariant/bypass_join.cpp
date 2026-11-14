#include <iostream>
#include <fstream>
#include <sstream>
#include <array>
#include <map>
#include <vector>
#include <set>
#include <algorithm>
#include <cstdlib>
using namespace std;
struct A {int w,d,n;};
int main(int argc,char**argv){
 if(argc<4)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,ST=argc>4?atoi(argv[4]):200;
 map<int,array<A,2>> rows;vector<int> states;int q,b,w,n;char d;
 while(in>>q>>b>>w>>d>>n){rows[q][b]={w,d=='R'?1:-1,n};}
 for(auto const&kv:rows)states.push_back(kv.first);
 map<int,array<vector<int>,2>> pats;ifstream pin(argv[3]);int p;while(pin>>q>>p)pats[q][p>>K&1].push_back(p);
 set<int> forbidden={74};
 vector<A> acts;for(int n:states)for(int w=0;w<2;w++)for(int d:{-1,1})acts.push_back({w,d,n});
 for(int a:states){if(forbidden.count(a))continue;vector<pair<int,int>> preds;bool bad=false;
  for(int q:states)for(int b:{0,1})if(rows[q][b].n==a){if(q==a||forbidden.count(q)){bad=true;break;}preds.push_back({q,b});} 
  if(bad||preds.empty())continue;set<pair<int,int>> changes(preds.begin(),preds.end());vector<vector<pair<A,int>>> options;
  for(auto[q,b]:preds){vector<pair<A,int>> opts;auto ps=pats[q][b];if(ps.empty()){bad=true;break;}
   for(auto first:acts){if(first.n==a)continue;bool okay=true;int maxst=0;
    for(int p:ps){struct Target {int q,h,t;};vector<Target>targets;
     int oq=q,oh=0,ot=p;
     for(int os=0;os<=24;os++){
      if(os>=2&&oq!=a)targets.push_back({oq,oh,ot});
      if((os>0&&changes.count({oq,(oh>=-K&&oh<=K)?((ot>>(K+oh))&1):0}))||oh < -K||oh>K||!rows.count(oq))break;
      A oa=rows[oq][(ot>>(K+oh))&1];ot=(ot&~(1<<(K+oh)))|(oa.w<<(K+oh));oh+=oa.d;oq=oa.n;
     }
     if(targets.empty()){okay=false;break;}
     int s=first.n,ch=first.d,ct=(p&~(1<<K))|(first.w<<K);bool hit=false;
     for(int st=1;st<=ST;st++){
      for(auto t:targets)if(s==t.q&&ch==t.h&&ct==t.t){hit=true;break;}if(hit){maxst=max(maxst,st);break;}
      if(ch < -K||ch>K||s==a||!rows.count(s))break;int cb=(ct>>(K+ch))&1;if(changes.count({s,cb}))break;A op=rows[s][cb];ct=(ct&~(1<<(K+ch)))|(op.w<<(K+ch));ch+=op.d;s=op.n;
     }
     if(!hit){okay=false;break;}
    }
    if(okay)opts.push_back({first,maxst});
   }
   options.push_back(opts);if(opts.empty()){bad=true;break;}
  }
  if(!bad){cout<<"{\"removed\":"<<a<<",\"changes\":[";bool comma=false;int ix=0;for(auto[q,b]:preds){if(comma)cout<<',';comma=true;cout<<"{\"row\":["<<q<<','<<b<<"],\"choices\":[";bool cm=false;for(auto[op,st]:options[ix++]){if(cm)cout<<',';cm=true;cout<<'['<<op.w<<','<<op.d<<','<<op.n<<','<<st<<']';}cout<<"]}";}cout<<"]}"<<endl;}
 }
}
