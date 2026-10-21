// Deterministic bounded single-state fold search. C++17, standard library only.
// This is a discovery filter, not a proof kernel or a minimum-state theorem.
// For every ordered pair (keep,drop), enumerate inherited keeper rows; when
// exactly one mapped branch agrees, allow every write/move/remaining target
// for the other branch. All other rows are exact copies with drop->keep.
// The radius-r window invariant overapproximates all initial tapes at start.
// A rejection means no positive common-endpoint diagram was found in the
// specified window/fuel. Survivors require an independent complete checker.
#include <algorithm>
#include <array>
#include <chrono>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Act { int w,d,z; bool operator==(const Act&a)const{return tie(w,d,z)==tie(a.w,a.d,a.z);} bool operator<(const Act&a)const{return tie(w,d,z)<tie(a.w,a.d,a.z);} };
struct Conf{int q,h,m;};
struct Path{vector<Conf> v; bool halt=false;};
struct Table{vector<array<Act,2>> t; vector<int> labels; int start,halt;};
Table read_table(string path){
 ifstream in(path); if(!in)throw runtime_error("cannot open table");
 map<pair<int,int>,Act> a;set<int> qs;int start=-1;string s;
 while(getline(in,s)){if(s.rfind("#! start ",0)==0){start=stoi(s.substr(9));continue;}if(s.empty()||s[0]=='#')continue;istringstream is(s);int q,b,w,z;char d;if(!(is>>q>>b>>w>>d>>z)||b<0||b>1||w<0||w>1||(d!='R'&&d!='L'))throw runtime_error("bad row");if(!a.emplace(make_pair(q,b),Act{w,d=='R'?1:-1,z}).second)throw runtime_error("duplicate row");qs.insert(q);}
 if(!qs.count(start)||a.size()!=2*qs.size())throw runtime_error("non-total table");
 set<int> halts;for(auto&kv:a)if(!qs.count(kv.second.z))halts.insert(kv.second.z);if(halts.size()!=1)throw runtime_error("not one halt");
 Table out;out.labels=vector<int>(qs.begin(),qs.end());out.labels.push_back(*halts.begin());map<int,int> idx;for(int i=0;i<(int)out.labels.size();i++)idx[out.labels[i]]=i;out.halt=out.labels.size()-1;out.start=idx[start];out.t.resize(out.halt);for(auto&kv:a){auto ac=kv.second;ac.z=idx[ac.z];out.t[idx[kv.first.first]][kv.first.second]=ac;}return out;
}
int main(int argc,char**argv){try{
 if(argc<5 || argc>7)throw runtime_error("usage: fold_search TABLE OUTPUT_PREFIX RADIUS FUEL [inherited|independent] [all|blank]");
 bool independent=argc>=6 && string(argv[5])=="independent";
 bool blank=argc==7 && string(argv[6])=="blank";
 string input=argv[1],prefix=argv[2];int r=stoi(argv[3]),fuel=stoi(argv[4]);if(r<1||r>9||fuel<1||fuel>1000)throw runtime_error("bad bounds");
 auto begin=chrono::steady_clock::now();Table O=read_table(input);int n=O.halt,width=2*r+1,count=1<<width,mask=count-1;
 vector<vector<unsigned char>> seen(n+1,vector<unsigned char>(count));deque<pair<int,int>> todo;
 int seeds=blank?1:count;
 for(int m=0;m<seeds;m++){seen[O.start][m]=1;todo.emplace_back(O.start,m);}long long contexts=seeds;
 while(!todo.empty()){auto [q,m]=todo.front();todo.pop_front();if(q==n)continue;Act a=O.t[q][(m>>r)&1];int x=(m&~(1<<r))|(a.w<<r),u,v;if(a.d==1){u=x>>1;v=u|(1<<(width-1));}else{u=(x<<1)&mask;v=u|1;}for(int y:{u,v})if(!seen[a.z][y]){seen[a.z][y]=1;contexts++;todo.emplace_back(a.z,y);}}
 vector<array<vector<int>,2>> words(n);for(int q=0;q<n;q++)for(int m=0;m<count;m++)if(seen[q][m])words[q][(m>>r)&1].push_back(m);
 for(auto&bs:words)for(auto&v:bs)if(v.size()>2)rotate(v.begin()+1,v.end()-1,v.end());
 vector<unique_ptr<Path>> paths((long long)n*count);
 auto path=[&](int q,int m)->Path&{auto&ptr=paths[(long long)q*count+m];if(!ptr){ptr=make_unique<Path>();int h=0;for(int k=0;k<fuel;k++){if(q==n||h< -r||h>r)break;Act a=O.t[q][(m>>(h+r))&1];m=(m&~(1<<(h+r)))|(a.w<<(h+r));h+=a.d;q=a.z;ptr->v.push_back({q,h,m});if(q==n)ptr->halt=true;}}return *ptr;};
 long long attempts=0,inherited=0,free_action=0,rejected=0,survivors=0,patterns=0;map<string,long long> reasons;ofstream hits(prefix+".hits.jsonl");
 auto mapped=[&](Act a,int keep,int drop){if(a.z==drop)a.z=keep;return a;};
 auto check=[&](int keep,int drop,const array<Act,2>&row,int selected=-1)->string{
  auto phi=[&](int q){return q==drop?keep:q;};
  for(int q:{keep,drop})for(int b=0;b<2;b++){
   if(selected!=-1 && b!=selected)continue;
   if(row[b]==mapped(O.t[q][b],keep,drop))continue;
   for(int word:words[q][b]){patterns++;Path&p=path(q,word);int nq=keep,nh=0,nm=word;bool join=false;vector<Conf> visited;
    for(int tick=0;tick<fuel;tick++){
     if(nq==n||nh< -r||nh>r)return "exit_window";
     for(auto&c:visited)if(c.q==nq&&c.h==nh&&c.m==nm)return "cycle";
     visited.push_back({nq,nh,nm});int bit=(nm>>(nh+r))&1;if(selected!=-1 && nq==keep && bit!=selected)return "cross_branch";Act a=nq==keep?row[bit]:mapped(O.t[nq][bit],keep,drop);nm=(nm&~(1<<(nh+r)))|(a.w<<(nh+r));nh+=a.d;nq=a.z;
     if(nq==n){if(!p.halt)return "new_halt";join=true;break;}
     for(auto&c:p.v)if(phi(c.q)==nq&&c.h==nh&&c.m==nm){join=true;break;}
     if(join)break;
    }
    if(!join)return "fuel";
   }
  }return "PASS";
 };
 auto test=[&](int keep,int drop,array<Act,2> row,bool free){attempts++;if(free)free_action++;else inherited++;string reason=check(keep,drop,row);reasons[reason]++;if(reason!="PASS"){rejected++;return;}survivors++;int k=O.labels[keep],d=O.labels[drop];hits<<"{\"id\":"<<attempts<<",\"keep\":"<<k<<",\"drop\":"<<d<<",\"family\":\""<<(free?"one_common_action":"inherited")<<"\",\"rows\":[";for(int b=0;b<2;b++){if(b)hits<<",";Act a=row[b];hits<<"["<<a.w<<","<<a.d<<","<<O.labels[a.z]<<"]";}hits<<"]}\n";hits.flush();ofstream out(prefix+".survivor-"+to_string(attempts)+".tm");out<<"#! start "<<O.labels[O.start==drop?keep:O.start]<<"\n";for(int q=0;q<n;q++)if(q!=drop)for(int b=0;b<2;b++){Act a=q==keep?row[b]:mapped(O.t[q][b],keep,drop);out<<O.labels[q]<<" "<<b<<" "<<a.w<<" "<<(a.d==1?'R':'L')<<" "<<O.labels[a.z]<<"\n";}cerr<<"SURVIVOR "<<input<<" "<<k<<" "<<d<<" "<<attempts<<"\n";};
 long long branch_attempts=0;
 for(int keep=0;keep<n;keep++)for(int drop=0;drop<n;drop++)if(keep!=drop){
  if(independent){
   array<vector<Act>,2> legal;
   for(int b=0;b<2;b++){
    if(b==1 && legal[0].empty())break;
    array<Act,2> row={mapped(O.t[keep][0],keep,drop),mapped(O.t[keep][1],keep,drop)};
    for(int w=0;w<2;w++)for(int d:{-1,1})for(int z=0;z<=n;z++)if(z!=drop){
     row[b]={w,d,z};branch_attempts++;string reason=check(keep,drop,row,b);if(reason=="PASS")legal[b].push_back(row[b]);
    }
   }
   for(Act a0:legal[0])for(Act a1:legal[1])test(keep,drop,{a0,a1},true);
   continue;
  }
  array<vector<Act>,2> a;for(int b=0;b<2;b++){a[b]={mapped(O.t[keep][b],keep,drop),mapped(O.t[drop][b],keep,drop)};sort(a[b].begin(),a[b].end());a[b].erase(unique(a[b].begin(),a[b].end()),a[b].end());}
  for(Act a0:a[0])for(Act a1:a[1])test(keep,drop,{a0,a1},false);
  if((a[0].size()==1)!=(a[1].size()==1)){int fixed=a[0].size()==1?0:1,other=1-fixed;for(int w=0;w<2;w++)for(int d:{-1,1})for(int z=0;z<=n;z++)if(z!=drop){Act ac{w,d,z};if(find(a[other].begin(),a[other].end(),ac)!=a[other].end())continue;array<Act,2> row;row[fixed]=a[fixed][0];row[other]=ac;test(keep,drop,row,true);}}
 }
 double sec=chrono::duration<double>(chrono::steady_clock::now()-begin).count();ofstream out(prefix+".json");out<<"{\n  \"initial_domain\":\""<<(blank?"blank_window":"all_tapes")<<"\",\n  \"mode\":\""<<(independent?"independent_branches":"inherited_or_one_common_action")<<"\",\n  \"branch_attempts\":"<<branch_attempts<<",\n  \"status\":\"COMPLETE_BOUNDED_SEARCH\",\n  \"states\":"<<n<<",\n  \"radius\":"<<r<<",\n  \"fuel\":"<<fuel<<",\n  \"ordered_pairs\":"<<(long long)n*(n-1)<<",\n  \"attempts\":"<<attempts<<",\n  \"inherited_attempts\":"<<inherited<<",\n  \"one_common_action_attempts\":"<<free_action<<",\n  \"filter_rejected\":"<<rejected<<",\n  \"filter_survivors\":"<<survivors<<",\n  \"invariant_contexts_including_halt\":"<<contexts<<",\n  \"tested_pattern_instances\":"<<patterns<<",\n  \"seconds\":"<<sec<<",\n  \"reasons\":{";bool first=true;for(auto&kv:reasons){if(!first)out<<",";first=false;out<<"\""<<kv.first<<"\":"<<kv.second;}out<<"},\n  \"scope\":\"All ordered keep/drop pairs. In inherited_or_one_common_action mode: inherited rows plus arbitrary other-branch action if exactly one mapped branch is shared. In independent_branches mode: arbitrary actions for both branches, but each positive new block must avoid reading the opposite keeper branch before joining; a candidate is then checked jointly. All unchanged rows map drop to keep. In blank_window domain the initial window is zero, with arbitrary new exterior bits during closure; all_tapes starts from every window. Failures are bounded diagram failures, not counterexamples or lower bounds. Survivors require independent checking.\"\n}\n";cout<<input<<" attempts="<<attempts<<" survivors="<<survivors<<" seconds="<<sec<<"\n";
 }catch(const exception&e){cerr<<e.what()<<"\n";return 1;}}
