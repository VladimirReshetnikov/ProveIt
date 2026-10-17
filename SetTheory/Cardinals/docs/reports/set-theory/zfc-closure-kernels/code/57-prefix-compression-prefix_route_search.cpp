#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
constexpr int WIDTH=2048, OFFSET=512;
struct Row{int w=-1,d=0,t=-1;};
struct Case{int id,r,h,oh,cost;bitset<WIDTH> initial,target;};
array<array<Row,2>,255> table;
vector<Case> cases;
struct Result{int kind,index,cost;unsigned conflict;};
long long checks=0;
Result run(Case const& c,int dead,array<int,510> const& variables,vector<Row> const& actions){
 int q=75,h=c.h;auto tape=c.initial;unsigned read=0;
 for(int step=0;step<10000;step++){
  if(q==96&&h==c.oh&&tape==c.target)return{0,-1,step,read};
  if(q==254||q==dead||h<0||h>=WIDTH)return{1,-1,step,read};
  int b=tape[h],j=variables[2*q+b];Row a=table[q][b];
  if(j>=0){read|=(1u<<j);a=actions[j];if(a.t<0)return{2,j,step,read};}
  if(a.t<0)return{1,-1,step,read};
  tape[h]=a.w;h+=a.d;q=a.t;
 }
 return{1,-1,10000,read};
}
int main(int argc,char**argv){
 if(argc!=2){cerr<<"usage: prefix_route_search DIRECTORY\n";return 2;}
 string dir=argv[1];ifstream tf(dir+"/table.tm");string line;
 while(getline(tf,line)){if(line.empty()||line[0]=='#')continue;istringstream ss(line);int q,b,w,t;char d;ss>>q>>b>>w>>d>>t;table[q][b]={w,d=='R'?1:-1,t};}
 ifstream cf(dir+"/cases.txt");Case c;int n,m;
 while(cf>>c.id>>c.r>>c.h>>c.oh>>n>>m){c.h+=OFFSET;c.oh+=OFFSET;c.initial.reset();c.target.reset();int x;for(int i=0;i<n;i++){cf>>x;c.initial[x+OFFSET]=true;}for(int i=0;i<m;i++){cf>>x;c.target[x+OFFSET]=true;}cases.push_back(c);}
 assert(cases.size()==17325);array<int,510> empty;empty.fill(-1);
 for(Case& c:cases){auto r=run(c,-1,empty,{});assert(r.kind==0);c.cost=r.cost;}
 cout<<"BASELINE all "<<cases.size()<<" concrete continuation samples passed\n"<<flush;
 vector<int> states;for(int q=0;q<254;q++)if(table[q][0].t>=0)states.push_back(q);
 long long nodes=0,pruned=0,survivors=0;auto started=chrono::steady_clock::now();
 ofstream result(dir+"/search.jsonl");
 for(int dead:{85,97,112,131}){
  vector<int> incoming;for(int q:states)if(q!=dead)for(int b=0;b<2;b++)if(table[q][b].t==dead)incoming.push_back(2*q+b);
  assert(incoming.size()<=2);array<int,510> variables;variables.fill(-1);for(int j=0;j<int(incoming.size());j++)variables[incoming[j]]=j;
  vector<Row> actions(incoming.size());long long family_nodes=0,family_checks=0,family_survivors=0,backjumps=0;
  auto descend=[&](auto&& self)->unsigned{
   nodes++;family_nodes++;
   for(Case const& c:cases){
    auto r=run(c,dead,variables,actions);checks++;family_checks++;
    if(r.kind==1){pruned++;return r.conflict;}
    if(r.kind==2){
     int j=r.index;unsigned union_conflict=0;
     for(int w=0;w<2;w++)for(int d:{-1,1})for(int t=0;t<=254;t++)if(t!=dead&&(t==254||table[t][0].t>=0)){
      actions[j]={w,d,t};unsigned conflict=self(self);actions[j]=Row{};
      if(conflict==0xffffffffu)return conflict;
      if(!(conflict&(1u<<j))){backjumps++;return conflict;}
      union_conflict|=(conflict&~(1u<<j));
     }
     return union_conflict;
    }
   }
   survivors++;family_survivors++;
   string stem="candidate_"+to_string(dead)+"_"+to_string(family_survivors);
   ofstream out(dir+"/"+stem+".tm");out<<"#! start 64\n";
   for(int q:states)if(q!=dead)for(int b=0;b<2;b++){int j=variables[2*q+b];Row a=j<0?table[q][b]:actions[j];if(a.t<0){a=table[q][b];a.t=254;}assert(a.t>=0&&a.t!=dead);out<<q<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.t<<'\n';}
   cout<<"SURVIVOR "<<stem<<'\n'<<flush;
   // Continue all branches after recording a full sample survivor.
   return (1u<<incoming.size())-1;
  };
  descend(descend);
  result<<"{\"deleted\":"<<dead<<",\"incoming\":"<<incoming.size()<<",\"nodes\":"<<family_nodes<<",\"checks\":"<<family_checks<<",\"survivors\":"<<family_survivors<<",\"backjumps\":"<<backjumps<<"}\n"<<flush;
  cout<<"DONE deletion "<<dead<<" nodes="<<family_nodes<<" checks="<<family_checks<<" survivors="<<family_survivors<<'\n'<<flush;
 }
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-started).count();
 ofstream summary(dir+"/summary.json");summary<<"{\"baseline_samples\":"<<cases.size()<<",\"nodes\":"<<nodes<<",\"checks\":"<<checks<<",\"survivors\":"<<survivors<<",\"seconds\":"<<seconds<<"}\n";
}
