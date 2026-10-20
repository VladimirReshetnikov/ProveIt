// Bounded closed-macro interval DP. No TM or mathematical proof inference.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
struct Node {int l=-1,r=-1,lead=0,z=0,depth=0;bool base=false;vector<int> added;};
vector<Node> nodes;
unordered_map<uint64_t,int> pairs;
uint64_t key(int l,int r){return (uint64_t(uint32_t(l))<<32)|uint32_t(r);}
vector<int> unite(const vector<int>&a,const vector<int>&b){vector<int>v;v.reserve(a.size()+b.size());set_union(a.begin(),a.end(),b.begin(),b.end(),back_inserter(v));return v;}
int make_node(int l,int r){auto k=key(l,r);auto it=pairs.find(k);if(it!=pairs.end())return it->second;Node n;n.l=l;n.r=r;n.lead=1+nodes[l].lead;n.z=max({n.lead,nodes[l].z,nodes[r].z});n.depth=1+max(nodes[l].depth,nodes[r].depth);n.added=unite(nodes[l].added,nodes[r].added);int id=nodes.size();n.added.push_back(id);nodes.push_back(move(n));pairs[k]=id;return id;}
bool better(int a,int b){auto &x=nodes[a],&y=nodes[b];if(x.added.size()!=y.added.size())return x.added.size()<y.added.size();if(x.depth!=y.depth)return x.depth<y.depth;return a<b;}
struct State {vector<vector<int>> bylead;};
struct Best {int id,global;string word;};
int main(){ios::sync_with_stdio(false);cin.tie(nullptr);
 int N,H,W,R,base_count,old_count,beam,zero,seconds;cin>>N>>H>>W>>R>>base_count>>old_count>>beam>>zero>>seconds;
 for(int i=0;i<N;i++){Node n;int b;cin>>n.l>>n.r>>b;n.base=b;if(n.l>=0){auto &a=nodes[n.l],&c=nodes[n.r];n.lead=1+a.lead;n.z=max({n.lead,a.z,c.z});n.depth=1+max(a.depth,c.depth);n.added=unite(a.added,c.added);pairs[key(n.l,n.r)]=i;}if(!n.base)n.added.push_back(i);nodes.push_back(move(n));}
 int mid[6];for(int &x:mid)cin>>x;vector<pair<int,int>>ctx(H);for(auto &p:ctx)cin>>p.first>>p.second;
 vector<string>words(W);set<string>allset;for(auto &w:words){cin>>w;for(int i=0;i<int(w.size());i++)for(int len=1;i+len<=int(w.size());len++)allset.insert(w.substr(i,len));}
 unordered_map<string,vector<int>>reuse;for(int i=0;i<R;i++){string w;int id;cin>>w>>id;reuse[w].push_back(id);}
 vector<string>all(allset.begin(),allset.end());sort(all.begin(),all.end(),[](auto&a,auto&b){return a.size()!=b.size()?a.size()<b.size():a<b;});
 unordered_map<string,State>dp;dp.reserve(all.size()*2);long long combinations=0,insertions=0;int processed=0,recipes=0;bool capped=false;vector<Best>best;
 auto begin=chrono::steady_clock::now();auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-begin).count();};
 auto insert=[&](State&st,int id){auto &n=nodes[id];if(n.z>zero||n.lead>zero)return;auto &v=st.bylead[n.lead];if(find(v.begin(),v.end(),id)!=v.end())return;v.push_back(id);sort(v.begin(),v.end(),better);if(int(v.size())>beam)v.pop_back();insertions++;};
 for(auto &w:all){
  if(processed%100==0&&elapsed()>=seconds){capped=true;break;}
  State st;st.bylead.resize(zero+1);
  if(w.size()==1){auto k=string("abcFIQ").find(w[0]);if(k==string::npos)return 4;insert(st,mid[k]);}
  if(reuse.count(w))for(int id:reuse[w])insert(st,id);
  for(int split=1;split<int(w.size());split++){
   auto &a=dp.at(w.substr(0,split));auto &b=dp.at(w.substr(split));
   for(int dl=0;dl<zero;dl++)for(int l:a.bylead[dl])for(int dr=0;dr<=zero;dr++)for(int r:b.bylead[dr]){
    combinations++;int lead=dl+1,depth=1+max(nodes[l].depth,nodes[r].depth);auto &v=st.bylead[lead];
    auto it=pairs.find(key(l,r));int existing=it==pairs.end()?-1:it->second;
    if(existing>=0){insert(st,existing);continue;}
    if(int(v.size())==beam&&max(nodes[l].added.size(),nodes[r].added.size())+1>nodes[v.back()].added.size())continue;
    auto uni=unite(nodes[l].added,nodes[r].added);size_t cost=uni.size()+1;
    if(int(v.size())==beam&&(cost>nodes[v.back()].added.size()||(cost==nodes[v.back()].added.size()&&depth>=nodes[v.back()].depth)))continue;
    insert(st,make_node(l,r));
   }
  }
  dp.emplace(w,move(st));processed++;
  if(processed%10000==0)cerr<<"intervals "<<processed<<" nodes "<<nodes.size()<<" pairs "<<combinations<<" seconds "<<elapsed()<<"\n";
 }
 for(auto &w:words){auto it=dp.find(w);if(it==dp.end())continue;recipes++;
  for(auto &v:it->second.bylead)for(int id:v){int cur=id;for(auto [side,sib]:ctx)cur=side==0?make_node(cur,sib):make_node(sib,cur);if(nodes[cur].z>zero)continue;
   bool dup=false;for(auto &x:best)if(x.global==cur)dup=true;if(dup)continue;
   bool improved=best.empty()||better(cur,best.front().global);
   best.push_back({id,cur,w});sort(best.begin(),best.end(),[](auto&a,auto&b){return better(a.global,b.global);});if(best.size()>16)best.pop_back();
   if(improved)cerr<<"BEST dag "<<base_count+nodes[cur].added.size()<<" depth "<<nodes[cur].depth<<" zero "<<nodes[cur].z<<" word "<<w<<"\n";
  }
 }
 auto expr=[&](auto&&self,int id)->void{if(id<N){cout<<id;return;}cout<<'[';self(self,nodes[id].l);cout<<',';self(self,nodes[id].r);cout<<']';};
 cout<<"{\"status\":\""<<(capped?"BOUNDED_DP_PARTIAL":"BOUNDED_DP_FAMILY_COMPLETE")<<"\",\"intervals\":"<<all.size()<<",\"processed\":"<<processed<<",\"recipes_evaluated\":"<<recipes<<",\"join_combinations\":"<<combinations<<",\"retention_events\":"<<insertions<<",\"interned_nodes\":"<<nodes.size()<<",\"seconds\":"<<elapsed()<<",\"beam\":"<<beam<<",\"zero_limit\":"<<zero<<",\"base_count\":"<<base_count<<",\"candidates\":[";
 for(int k=0;k<int(best.size());k++){if(k)cout<<',';auto &x=best[k];auto &n=nodes[x.global];cout<<"{\"word\":\""<<x.word<<"\",\"dag_nodes\":"<<base_count+n.added.size()<<",\"maximum_depth\":"<<n.depth<<",\"maximum_zero_run\":"<<n.z<<",\"replacement_leading_zero_run\":"<<nodes[x.id].lead<<",\"replacement\":";expr(expr,x.id);cout<<'}';}
 cout<<"]}\n";
}
