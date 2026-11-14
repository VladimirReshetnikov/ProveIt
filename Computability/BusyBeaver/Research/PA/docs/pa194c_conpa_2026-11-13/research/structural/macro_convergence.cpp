// Bounded universal macro-convergence search for a complete binary TM.
// g++ -O3 -std=c++17 macro_convergence.cpp -o macro_convergence
// Usage: macro_convergence table K depth [context_file] [mode]
// mode: direct, shifted, marker, actions, all (default).
// Local abstract reachability starts from a radius-K all-zero window at state74.
// On each shift both possibilities for the unknown incoming boundary bit are
// added, a sound overapproximation of every blank-start run. All simulations
// must join before reading beyond the recorded window; finite enumeration then
// covers arbitrary exterior tapes. Negative outcomes imply no lower bound.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
struct A {int w,d,n;};
struct Good{int action,oldSteps,newSteps;set<int> visits;};
int main(int argc,char**argv){
 if(argc<4)return 2;
 int K=stoi(argv[2]),depth=stoi(argv[3]),W=2*K+1,N=1<<W,MASK=N-1;
 string mode=argc>5?argv[5]:"all";
 map<int,array<A,2>> rows;map<int,set<int>> incoming;int q,b,w,n;char d;
 ifstream input(argv[1]);string line;
 while(getline(input,line)){istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};incoming[n].insert(d=='R'?1:-1);}
 vector<int>states;for(auto const&x:rows)states.push_back(x.first);
 map<int,vector<int>>patterns;
 if(argc>4 && string(argv[4])!="-"){ifstream in(argv[4]);int p;while(in>>q>>p)patterns[q].push_back(p);}
 else{
  map<int,vector<bool>>seen;queue<pair<int,int>>todo;for(int q:states)seen[q]=vector<bool>(N);
  auto add=[&](int q,int p){if(!rows.count(q)||seen[q][p])return;seen[q][p]=true;todo.emplace(q,p);};
  add(74,0);
  while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);
   if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
  for(int q:states)for(int p=0;p<N;p++)if(seen[q][p])patterns[q].push_back(p);
 }
 for(int q:states)if(patterns[q].empty()){cerr<<"MISSING CONTEXTS "<<q<<endl;return 3;}
 auto key=[&](int q,int h,int t)->int64_t{return((int64_t(q)*64+h+K+4)*N+t);};
 long long pairs=0,checks=0,solutions=0;long long total=0;for(auto const&x:patterns)total+=x.second.size();
 cerr<<"States "<<states.size()<<" patterns "<<total<<" K "<<K<<" depth "<<depth<<endl;
 if(mode!="actions")for(int remove:states){if(remove==74)continue;
  vector<pair<int,int>>relations;
  if(mode=="all"||mode=="direct")relations.push_back({0,0});
  // Uniform arrival direction allows a head displacement of minus twice it;
  // independently toggling the just-written neighbour is also realizable.
  set<int>dirs;for(auto const&[q,acts]:rows)if(q!=remove)for(auto a:acts)if(a.n==remove)dirs.insert(a.d);
  int dir=dirs.size()==1?*dirs.begin():0;
  if(dir){if(mode=="all"||mode=="shifted")relations.push_back({-2*dir,0});if(mode=="all"||mode=="marker"){relations.push_back({0,1});relations.push_back({-2*dir,1});}}
  for(auto[shift,toggle]:relations)for(int keep:states){if(keep==remove)continue;pairs++;bool okay=true;int mo=0,mn=0;
   for(int p:patterns[remove]){checks++;unordered_map<int64_t,int>old;int c=remove,h=0,t=p;
    for(int st=1;st<=depth;st++){
     if(h < -K||h>K||!rows.count(c))break;A a=rows[c][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(a.w<<(h+K));h+=a.d;c=a.n;
     if(c==remove && toggle && (h-dir < -K||h-dir>K))continue;
     int mapped=c==remove?keep:c,mappedh=h+(c==remove?shift:0),mappedt=t^((c==remove&&toggle)?1<<(h-dir+K):0);
     auto ky=key(mapped,mappedh,mappedt);if(old.count(ky))break;old[ky]=st;
    }
    c=keep;h=shift;t=p^(toggle?1<<(K-dir):0);bool hit=false;
    for(int st=1;st<=depth;st++){
     if(h < -K||h>K||!rows.count(c))break;A a=rows[c][t>>(h+K)&1];bool target=a.n==remove;int nw=a.w^(target?toggle:0);t=(t&~(1<<(h+K)))|(nw<<(h+K));h+=a.d+(target?shift:0);c=target?keep:a.n;
     auto it=old.find(key(c,h,t));if(it!=old.end()){hit=true;mo=max(mo,it->second);mn=max(mn,st);break;}
    }
    if(!hit){okay=false;break;}
   }
   if(okay){solutions++;cout<<"{\"remove\":"<<remove<<",\"keep\":"<<keep<<",\"shift\":"<<shift<<",\"toggle\":"<<toggle<<",\"toggle_offset\":"<<-dir<<",\"old_steps\":"<<mo<<",\"new_steps\":"<<mn<<"}"<<endl;}
  }
 }
 if(mode=="all"||mode=="actions"){
  vector<A>actions;for(int n:states)for(int w:{0,1})for(int d:{-1,1})actions.push_back({w,d,n});
  map<int,array<map<int,Good>,2>>options;
  for(int q:states)for(int bit:{0,1}){
   vector<int>pats;for(int p:patterns[q])if((p>>K&1)==bit)pats.push_back(p);
   vector<unordered_map<int64_t,int>>traces;
   for(int p:pats){unordered_map<int64_t,int>trace;int c=q,h=0,t=p;
    for(int st=1;st<=depth;st++){
     if(h < -K||h>K||!rows.count(c))break;A a=rows[c][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(a.w<<(h+K));h+=a.d;c=a.n;auto ky=key(c,h,t);if(trace.count(ky))break;trace[ky]=st;
    }traces.push_back(move(trace));
   }
   for(int ai=0;ai<int(actions.size());ai++){
    A first=actions[ai];bool okay=true;Good good{ai,0,0,{}};
    for(int j=0;j<int(pats.size());j++){
     int p=pats[j],c=first.n,h=first.d,t=(p&~(1<<K))|(first.w<<K);bool hit=false;
     for(int st=1;st<=depth;st++){
      auto it=traces[j].find(key(c,h,t));if(it!=traces[j].end()){hit=true;good.oldSteps=max(good.oldSteps,it->second);good.newSteps=max(good.newSteps,st);break;}
      if(c==q||h < -K||h>K||!rows.count(c))break;good.visits.insert(c);A a=rows[c][t>>(h+K)&1];t=(t&~(1<<(h+K)))|(a.w<<(h+K));h+=a.d;c=a.n;
     }if(!hit){okay=false;break;}
    }if(okay)options[q][bit][ai]=good;
   }
  }
  for(int a:states)for(int b:states){if(a>=b||a==74||b==74)continue;array<vector<int>,2>choices;
   for(int bit:{0,1})for(auto const&[ai,g]:options[a][bit]){
    auto it=options[b][bit].find(ai);if(it==options[b][bit].end()||g.visits.count(b)||it->second.visits.count(a))continue;
    if(actions[ai].n==a||actions[ai].n==b)continue;choices[bit].push_back(ai);
   }
   if(choices[0].empty()||choices[1].empty())continue;solutions++;
   cout<<"{\"remove\":"<<a<<",\"keep\":"<<b<<",\"choices\":[";
   for(int bit:{0,1}){if(bit)cout<<',';cout<<'[';bool sep=false;for(int ai:choices[bit]){if(sep)cout<<',';sep=true;A op=actions[ai];cout<<'['<<op.w<<','<<op.d<<','<<op.n<<']';}cout<<']';}cout<<"]}"<<endl;
  }
 }
 cerr<<"SUMMARY pairs "<<pairs<<" contexts_checked "<<checks<<" solutions "<<solutions<<endl;
}
