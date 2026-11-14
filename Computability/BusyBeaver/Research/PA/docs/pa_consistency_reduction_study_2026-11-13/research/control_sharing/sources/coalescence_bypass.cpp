#include <cstdint>
#include <iostream>
#include <fstream>
#include <sstream>
#include <array>
#include <map>
#include <set>
#include <vector>
#include <algorithm>
#include <cstdlib>
#include <unordered_set>
using namespace std;
struct A{int w,d,n;};struct CT{int p;unordered_set<uint64_t> targets;bool halt=false;};
uint64_t key(int q,int h,int t){return uint64_t(q)<<32|uint64_t(h+32)<<24|t;}
int main(int argc,char**argv){
 if(argc<6)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,OLD=atoi(argv[3]),NEW=atoi(argv[4]);
 map<int,array<A,2>> rows;int q,b,w,n;char d;string line;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};}
 vector<int>states;map<int,array<vector<int>,2>>patterns;for(auto const&[q,aa]:rows)states.push_back(q);
 ifstream pin(argv[5]);int rq,rp;while(pin>>rq>>rp)patterns[rq][rp>>K&1].push_back(rp);
 vector<A>actions;for(int n:states)for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,n});actions.push_back({0,1,254});
 for(int a:states){if(a==74)continue;
  vector<pair<int,int>> incoming;for(int p:states)for(int bt=0;bt<2;bt++)if(p!=a&&rows[p][bt].n==a)incoming.push_back({p,bt});
  if(incoming.empty())continue;set<pair<int,int>> avoid(incoming.begin(),incoming.end());
  bool okay=true;vector<vector<A>>allchoices;
  for(auto [p,bt]:incoming){vector<A>choices;vector<CT> cs;
   for(int pat:patterns[p][bt]){CT ct;ct.p=pat;int c=p,h=0,t=pat;
    for(int st=1;st<=OLD;st++){
     if(h< -K||h>K||!rows.count(c))break;
     A op=rows[c][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
     if(c==254){ct.halt=true;break;}
     if(c!=a&&!ct.targets.insert(key(c,h,t)).second)break;
    }cs.push_back(move(ct));
   }
   for(A first:actions){if(first.n==a)continue;bool good=true;
    for(auto const&ct:cs){int pat=ct.p;int c=first.n,h=first.d,t=(pat&~(1<<K))|(first.w<<K);bool hit=false;
     for(int st=1;st<=NEW;st++){
      if((ct.halt&&c==254)||ct.targets.count(key(c,h,t))){hit=true;break;}
      if(c==a||h< -K||h>K||!rows.count(c))break;
      int read=t>>(h+K)&1;if(avoid.count({c,read}))break;
      A op=rows[c][read];t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;c=op.n;
     }if(!hit){good=false;break;}
    }if(good)choices.push_back(first);
   }
   if(choices.empty()){okay=false;break;}allchoices.push_back(choices);
  }
  if(okay){cout<<"{\"remove\":"<<a<<",\"rewrites\":[";for(size_t i=0;i<incoming.size();i++){if(i)cout<<',';cout<<"{\"row\":["<<incoming[i].first<<','<<incoming[i].second<<"],\"actions\":[";bool sep=false;for(A act:allchoices[i]){if(sep)cout<<',';sep=true;cout<<'['<<act.w<<','<<act.d<<','<<act.n<<']';}cout<<"]}";}cout<<"]}"<<endl;}
  cerr<<a<<" "<<(okay?"FOUND":"no")<<endl;
 }
}
