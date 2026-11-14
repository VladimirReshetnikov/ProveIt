#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Act{int w,d,n;};
vector<int> labels;map<int,int> ids;vector<array<Act,2>> tab;
vector<set<pair<int,int>>> inc;
int a,b,orientation,N;array<Act,2> acts;int mask;
vector<unsigned> seen;unsigned generation=0;
unsigned long long calls=0,runs=0,actions=0,pairs=0,steps=0;
array<vector<Act>,2> choices;
struct Result{int status;int len;}; // -1 fail, 0/1 missing row, 2 complete.
Result run(int source,int neighbor,int read){
 ++runs;auto old=tab[source][read];int wantq=old.n==a?b:old.n;
 int wanthead=old.d,wanttape=old.w+2*neighbor;
 int q=b,head=0,tape=read+2*neighbor,len=0;auto gen=++generation;if(!gen){fill(seen.begin(),seen.end(),0);gen=++generation;}
 while(true){
  if(len && q==wantq && head==wanthead && tape==wanttape)return{2,len};
  if((head!=0&&head!=-orientation)||q==N)return{-1,0};
  int readbit=head==0?(tape&1):((tape>>1)&1);
  if(q==b && !(mask&(1<<readbit)))return{readbit,0};
  int key=q*8+(head!=0)*4+tape;
  if(seen[key]==gen)return{-1,0};seen[key]=gen;
  Act z=q==b?acts[readbit]:tab[q][readbit];
  if(head==0)tape=(tape&2)+z.w;else tape=(tape&1)+2*z.w;
  head+=z.d;q=z.n==a?b:z.n;++len;++steps;
 }
}
bool solve(){
 ++calls;
 for(int p=0;p<2;p++)for(int r=0;r<2;r++){
  auto res=run(p?b:a,p,r);
  if(res.status<0)return false;
  if(res.status!=2){
   int bit=res.status;int oldmask=mask;mask|=1<<bit;
   for(auto z:choices[bit]){++actions;acts[bit]=z;if(solve())return true;}
   mask=oldmask;return false;
  }
 }
 return true;
}
bool initial_can_work(Act z,int bit){
 for(int p=0;p<2;p++){
  Act old=tab[p?b:a][bit];int wantq=old.n==a?b:old.n;
  bool target=z.n==wantq&&z.d==old.d&&z.w==old.w;
  if(!target&&(z.d==orientation||z.n==N))return false;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc!=3){cerr<<"usage: recursive_pairs INPUT.native.tm OUTPREFIX\n";return 2;}
 ifstream f(argv[1]);string line;vector<array<int,5>> raw;set<int> labels_set;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream ss(line);int q,r,w,n;char d;ss>>q>>r>>w>>d>>n;raw.push_back({q,r,w,d=='R'?1:-1,n});labels_set.insert(q);}
 labels.assign(labels_set.begin(),labels_set.end());N=labels.size();labels.push_back(254);
 for(int i=0;i<=N;i++)ids[labels[i]]=i;
 tab.resize(N);inc.resize(N+1);seen.assign(N*8,0);
 for(auto r:raw){tab[ids[r[0]]][r[1]]={r[2],r[3],ids[r[4]]};inc[ids[r[4]]].insert({r[2],r[3]});}
 auto started=chrono::steady_clock::now();
 for(int direction:{1,-1}){
  orientation=direction;
  vector<int> zero,one;
  for(int q=0;q<N;q++)if(labels[q]!=74){if(inc[q]==set<pair<int,int>>{{0,orientation}})zero.push_back(q);if(inc[q]==set<pair<int,int>>{{1,orientation}})one.push_back(q);}
  for(int qa:zero)for(int qb:one){
   a=qa;b=qb;++pairs;mask=0;choices[0].clear();choices[1].clear();
   for(int bit=0;bit<2;bit++)for(int w:{0,1})for(int d:{-1,1})for(int n=0;n<=N;n++)if(n!=a){Act z{w,d,n};if(initial_can_work(z,bit))choices[bit].push_back(z);}
   if(solve()){
    cout<<"FOUND "<<labels[a]<<" "<<labels[b]<<" "<<orientation<<"\n";
    ofstream out(string(argv[2])+".found.json");
    out<<"{\"deleted\":"<<labels[a]<<",\"keeper\":"<<labels[b]<<",\"entry_direction\":"<<orientation<<",\"actions\":[";
    for(int r=0;r<2;r++){if(r)out<<",";auto z=acts[r];out<<"["<<z.w<<","<<z.d<<","<<labels[z.n]<<"]";}
    out<<"],\"durations\":[";bool comma=false;for(int p=0;p<2;p++)for(int r=0;r<2;r++){if(comma)out<<",";comma=true;out<<run(p?b:a,p,r).len;}out<<"]}\n";
    return 0;
   }
   if(pairs%100==0)cout<<"PROGRESS "<<pairs<<" calls "<<calls<<" steps "<<steps<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
  }
 }
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-started).count();
 ofstream out(string(argv[2])+".receipt.json");out<<"{\"working_states\":"<<N<<",\"contextual_pairs\":"<<pairs<<",\"recursive_calls\":"<<calls<<",\"partial_case_runs\":"<<runs<<",\"row_assignments_tried\":"<<actions<<",\"simulated_steps\":"<<steps<<",\"survivors\":0,\"seconds\":"<<seconds<<",\"exact_cycle_detection\":true,\"recursive_keeper_rows_allowed\":true,\"scope\":\"Two-cell contextual folds of two states with opposite known neighbor bits, for either uniform incoming direction; all transitions of the keeper may be reassigned. Not a lower bound for arbitrary machines.\"}\n";
 cout<<"DONE pairs "<<pairs<<" calls "<<calls<<" steps "<<steps<<" seconds "<<seconds<<endl;
}
