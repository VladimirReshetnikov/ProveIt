#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <queue>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
struct Action {int w=-1,d=0,z=-1; bool operator==(Action b)const{return w==b.w&&d==b.d&&z==b.z;}};
struct Goal {unordered_set<uint64_t> points;bool halt=false;};
struct Search {
 array<array<Action,2>,1024> old{};vector<int> Q;
 int start=0,halt=254,r=7,fuel=97,width=15,M=32767,keep,drop,delta=0;
 vector<vector<uint8_t>> domain;vector<array<vector<int>,2>> patterns;
 unordered_map<uint64_t,Goal> cache;
 array<Action,2> a;array<bool,2> assigned{};vector<Action> actions;
 uint64_t checks=0,rejects=0,covered=0,hits=0,pairs=0;
 uint64_t partial_by_depth[3]={0,0,0};
 chrono::steady_clock::time_point begin;double seconds=300;string output;
 bool stopped=false;int only_keep=-1,only_drop=-1;
 uint64_t conf(int q,int h,int m)const{return (uint64_t(q)<<24)|(uint64_t(h+r+1)<<16)|uint64_t(m);}
 int phi(int q)const{return q==drop?keep:q;}
 void read(string filename){
  ifstream in(filename);string line;
  while(getline(in,line)){
   if(line.rfind("#! start ",0)==0){start=stoi(line.substr(9));continue;}
   if(line.empty()||line[0]=='#')continue;
   istringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;
   old[q][b]={w,d=='R'?1:-1,z};Q.push_back(q);
  }
  sort(Q.begin(),Q.end());Q.erase(unique(Q.begin(),Q.end()),Q.end());
 }
 string pattern_file;
 void initialize(){
  width=2*r+1;M=(1<<width)-1;patterns.resize(1024);
  ifstream in(pattern_file);int rr,n;in>>rr>>n;if(!in||rr!=r||n!=int(Q.size()))throw runtime_error("Context input mismatch");
  uint64_t count=0;
  for(int i=0;i<n;i++){int q,k,m;in>>q>>k;for(int j=0;j<k;j++){in>>m;patterns[q][(m>>r)&1].push_back(m);count++;}}
  if(!in)throw runtime_error("Bad context input");
  for(int q:Q)for(int b:{0,1})if(patterns[q][b].size()>2)rotate(patterns[q][b].begin()+1,patterns[q][b].end()-1,patterns[q][b].end());
  cerr<<"OBSERVED_CONTEXTS "<<count<<" (NOT AN INDUCTIVE DOMAIN)\n";
 }
 Goal& goals(int q,int m){
  uint64_t key=(uint64_t(q)<<16)|m;auto it=cache.find(key);if(it!=cache.end())return it->second;
  Goal g;int h=0;
  for(int tick=0;tick<fuel;tick++){
   if(q==halt||h < -r||h>r)break;
   auto v=old[q][(m>>(h+r))&1];m=(m&~(1<<(h+r)))|(v.w<<(h+r));h+=v.d;q=v.z;
   g.points.insert(conf(q,h,m));g.halt|=q==halt;
  }
  return cache.emplace(key,move(g)).first->second;
 }
 // -1 rejects, 0/1 demands the indicated unassigned branch, 2 passes.
 int check(){
  checks++;
  for(int stage:{0,1})for(int oq:{keep,drop})for(int b:{0,1}){
   auto x=old[oq][b];x.d+=(x.z==drop?delta:0);x.z=phi(x.z);
   if(oq!=drop&&assigned[b]&&a[b]==x)continue;
   size_t lo=stage==0?0:min(size_t(2),patterns[oq][b].size()), hi=stage==0?min(size_t(2),patterns[oq][b].size()):patterns[oq][b].size();
   for(size_t wi=lo;wi<hi;wi++){int word=patterns[oq][b][wi];
    auto& g=goals(oq,word);int q=keep,h=(oq==drop?delta:0),m=word;bool joined=false;
    for(int tick=0;tick<fuel;tick++){
     if(q==halt||h < -r||h>r)return -1;
     int nb=(m>>(h+r))&1;Action v;
     if(q==keep){if(!assigned[nb])return nb;v=a[nb];}else{v=old[q][nb];v.d+=(v.z==drop?delta:0);v.z=phi(v.z);}
     m=(m&~(1<<(h+r)))|(v.w<<(h+r));h+=v.d;q=v.z;
     if(q==halt){joined=g.halt;break;}
     if(g.points.count(conf(q,h,m))||(q==keep&&h-delta>=-r-1&&h-delta<=r+1&&g.points.count(conf(drop,h-delta,m)))){joined=true;break;}
    }
    if(!joined)return -1;
   }
  }
  return 2;
 }
 void save(){
  ofstream out(output);out<<"#! start "<<phi(start)<<"\n";
  for(int q:Q)if(q!=drop)for(int b:{0,1}){
   auto x=q==keep?a[b]:old[q][b];if(q!=keep)x.d+=(x.z==drop?delta:0);x.z=phi(x.z);
   out<<q<<' '<<b<<' '<<x.w<<' '<<(x.d==1?'R':'L')<<' '<<x.z<<'\n';
  }
  ofstream meta(output+".json");meta<<"{\"keep\":"<<keep<<",\"drop\":"<<drop<<",\"delta\":"<<delta<<",\"radius\":"<<r<<",\"fuel\":"<<fuel<<",\"rows\":[";
  for(int b:{0,1}){if(b)meta<<',';meta<<'['<<a[b].w<<','<<a[b].d<<','<<a[b].z<<']';}meta<<"]}\n";
 }
 void walk(){
  if(stopped)return;
  if((checks&8191)==0&&chrono::duration<double>(chrono::steady_clock::now()-begin).count()>seconds){stopped=true;return;}
  int result=check(),depth=assigned[0]+assigned[1];
  if(result==-1){rejects++;uint64_t c=1;for(int j=depth;j<2;j++)c*=actions.size();covered+=c;partial_by_depth[depth]++;return;}
  if(result==2){
   if(depth==2){hits++;string prefix=output;output=prefix+"-"+to_string(hits)+".tm";save();output=prefix;cerr<<"HIT "<<hits<<' '<<keep<<' '<<drop<<'\n';if(hits>=64)stopped=true;return;}
   result=!assigned[0]?0:1;
  }
  if(assigned[result]){cerr<<"BAD DEMAND\n";abort();}
  assigned[result]=true;
  for(auto x:actions){a[result]=x;walk();if(stopped)break;}
  assigned[result]=false;
 }
 void run(){
  begin=chrono::steady_clock::now();uint64_t total_expected=0;
  for(size_t i=0;i<Q.size();i++)for(size_t j=0;j<Q.size();j++)for(int shift:{-2,2}){
   if(i==j||Q[j]==start)continue;delta=shift;
   keep=Q[i];drop=Q[j];actions.clear();
   if(only_keep>=0&&(keep!=only_keep||drop!=only_drop))continue;
   bool eligible=true;for(int q:Q)if(q!=keep&&q!=drop)for(int b:{0,1})if(old[q][b].z==drop&&old[q][b].d+delta!=1&&old[q][b].d+delta!=-1)eligible=false;
   if(!eligible)continue;
   for(int w:{0,1})for(int d:{-1,1}){for(int q:Q)if(q!=drop)actions.push_back({w,d,q});actions.push_back({w,d,halt});}
   assigned={false,false};uint64_t before=covered+hits;walk();pairs++;
   if(!stopped&&covered+hits-before!=actions.size()*actions.size()){cerr<<"BAD COVERAGE\n";abort();}
   total_expected+=actions.size()*actions.size();
   if(pairs%100==0||stopped)cerr<<"PROGRESS "<<pairs<<" pair="<<keep<<":"<<drop<<" partial="<<checks<<" covered="<<covered<<" cached="<<cache.size()<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<'\n';
   if(stopped)goto done;
  }
  done:
  cout<<"{\"status\":\""<<(hits?"HIT":stopped?"TIME_LIMIT":"COMPLETE")<<"\",\"pairs\":"<<pairs<<",\"partial_checks\":"<<checks<<",\"rejection_leaves\":"<<rejects<<",\"covered_rejections\":"<<covered<<",\"expected_tables_for_started_pairs\":"<<total_expected<<",\"pruned_depths\":["<<partial_by_depth[0]<<','<<partial_by_depth[1]<<','<<partial_by_depth[2]<<"],\"hits\":"<<hits<<",\"delta\":"<<delta<<",\"radius\":"<<r<<",\"fuel\":"<<fuel<<",\"states\":"<<Q.size()<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<"}\n";
 }
};
int main(int argc,char**argv){
 if(argc<3){cerr<<"usage: full_two_row INPUT OUTPUT [SECONDS] [RADIUS]\n";return 1;}
 Search s;s.read(argv[1]);s.output=argv[2];if(argc>3)s.seconds=stod(argv[3]);if(argc>4)s.r=stoi(argv[4]);if(argc<6)throw runtime_error("Need context file as argument5");s.pattern_file=argv[5];s.initialize();s.run();
}
