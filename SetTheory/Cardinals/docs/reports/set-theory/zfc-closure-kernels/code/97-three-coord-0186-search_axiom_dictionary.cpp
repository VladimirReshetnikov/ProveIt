// Source-level AX symmetry search, October 2026. No TM correctness claim.
// Every dictionary word denotes an existing complete closed source program.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
using namespace std;
struct Token { string w; uint64_t lo,hi; int mask; };
struct Node { uint64_t lo,hi; int parts,prev,token,score; };
struct Gene { vector<int> order,role; };
vector<Token> dict;
array<vector<int>,256> first;
string prefix,suffix;
vector<array<string,6>> rows;
int core,beamwidth;
bool same(const Node&a,const Node&b) {return a.lo==b.lo&&a.hi==b.hi;}
int countbits(uint64_t a,uint64_t b) { return __builtin_popcountll(a)+__builtin_popcountll(b); }
pair<int,vector<int>> evaluate(const string&w) {
  vector<vector<int>> beams(w.size()+1);
  vector<Node> arena; arena.reserve(w.size()*beamwidth*3);
  arena.push_back({0,0,0,-1,-1,0});beams[0].push_back(0);
  for(size_t p=0;p<w.size();p++) {
    if(beams[p].empty())continue;
    vector<int> ts;
    for(int t:first[(unsigned char)w[p]]) {
      const auto&v=dict[t]; auto end=p+v.w.size();
      if(end>w.size()||w.compare(p,v.w.size(),v.w))continue;
      if(p==0&&end<w.size()&&!(v.mask&1))continue;
      if(end==w.size()&&p>0&&!(v.mask&2))continue;
      ts.push_back(t);
    }
    for(int prev:beams[p])for(int t:ts) {
      Node a=arena[prev];a.lo|=dict[t].lo;a.hi|=dict[t].hi;
      a.parts++;a.prev=prev;a.token=t;
      a.score=a.parts+countbits(a.lo,a.hi);
      auto &b=beams[p+dict[t].w.size()];
      bool dominated=false;
      for(int id:b){const auto&n=arena[id];
        if((n.lo&a.lo)==n.lo&&(n.hi&a.hi)==n.hi&&n.parts<=a.parts){dominated=true;break;}}
      if(dominated)continue;
      if(b.size()>=size_t(beamwidth)&&arena[b.back()].score<a.score)continue;
      int id=arena.size();arena.push_back(a);
      b.erase(remove_if(b.begin(),b.end(),[&](int j){const auto&n=arena[j];return (a.lo&n.lo)==a.lo&&(a.hi&n.hi)==a.hi&&a.parts<=n.parts;}),b.end());
      b.push_back(id);
      sort(b.begin(),b.end(),[&](int i,int j){const auto&a=arena[i];const auto&b=arena[j];return a.score!=b.score?a.score<b.score:a.parts<b.parts;});
      if(b.size()>size_t(beamwidth))b.pop_back();
    }
  }
  if(beams.back().empty())return {10000,{}};
  int id=beams.back().front(),cost=arena[id].score+core-1;
  vector<int> parts;
  while(arena[id].prev>=0){parts.push_back(arena[id].token);id=arena[id].prev;}
  reverse(parts.begin(),parts.end());return {cost,parts};
}
string spelling(const Gene&g){string w=prefix;for(int i:g.order)w+=rows[i][g.role[i]];return w+suffix;}
void save(ofstream&out,int cost,long long trial,const Gene&g,const vector<int>&parts){
  out<<"{\"cost_upper_bound\":"<<cost<<",\"trial\":"<<trial<<",\"order\":[";
  for(size_t i=0;i<g.order.size();i++){if(i)out<<",";out<<g.order[i];}out<<"],\"roles\":[";
  for(size_t i=0;i<g.role.size();i++){if(i)out<<",";out<<g.role[i];}out<<"],\"parts\":[";
  for(size_t i=0;i<parts.size();i++){if(i)out<<",";out<<"\""<<dict[parts[i]].w<<"\"";}
  out<<"]}"<<endl;
}
int main(int argc,char**argv){
  if(argc<6){cerr<<"input output seconds seed beam [enumerate|random|mutate]"<<endl;return 2;}
  ifstream in(argv[1]);ofstream out(argv[2]);int n,priv;in>>n>>core>>priv;
  for(int i=0;i<n;i++){Token t;in>>t.w>>t.lo>>t.hi>>t.mask;dict.push_back(t);first[(unsigned char)t.w[0]].push_back(i);}
  int nr;in>>prefix>>suffix>>nr;rows.resize(nr);for(auto&row:rows)for(auto&w:row)in>>w;
  const double limit=stod(argv[3]);mt19937_64 rng(stoull(argv[4]));beamwidth=stoi(argv[5]);string mode=argc>6?argv[6]:"enumerate";
  Gene g,incumbent;g.order.resize(nr);g.role.resize(nr);iota(g.order.begin(),g.order.end(),0);fill(g.role.begin(),g.role.end(),0);incumbent=g;
  int best=10000,incumbentcost=10000;long long trial=0,saved=0;
  const auto start=chrono::steady_clock::now();double elapsed=0;
  do{
    auto ans=evaluate(spelling(g));
    if(ans.first<best){best=ans.first;cerr<<"BEST "<<best<<" trial "<<trial<<" sec "<<elapsed<<endl;}
    if(ans.first<=best+1&&saved<5000){save(out,ans.first,trial,g,ans.second);saved++;}
    if(ans.first<=incumbentcost||(rng()%1000==0)){incumbent=g;incumbentcost=ans.first;}
    trial++;
    if(mode=="enumerate") {if(!next_permutation(g.order.begin(),g.order.end()))break;}
    else if(mode=="random") {iota(g.order.begin(),g.order.end(),0);shuffle(g.order.begin(),g.order.end(),rng);for(auto&r:g.role)r=rng()%6;}
    else {
      g=incumbent;
      int i=rng()%nr,j=rng()%nr;
      if(rng()%2)swap(g.order[i],g.order[j]);else g.role[i]=rng()%6;
      if(trial%300==0){iota(g.order.begin(),g.order.end(),0);fill(g.role.begin(),g.role.end(),0);}
      if(trial%1000==0){shuffle(g.order.begin(),g.order.end(),rng);for(auto&r:g.role)r=rng()%6;}
    }
    elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  }while(elapsed<limit);
  cerr<<"DONE "<<trial<<" best "<<best<<" saved "<<saved<<" seconds "<<elapsed<<endl;
}
