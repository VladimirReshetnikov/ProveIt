// Adapted from compression/prefix_route_search.cpp in this research session.
// Exhaustive lazy synthesis of two rows in one fresh repair state.
#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <chrono>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
constexpr int WIDTH=2048, OFFSET=512, NEW=255;
int START=0;
struct Row{int w=-1,d=0,t=-1;};
struct Case{int id,r,h,oh;bitset<WIDTH> initial;array<bitset<WIDTH>,3> target;};
array<array<Row,2>,256> table;
vector<Case> cases;
struct Result{int kind,index,cost;unsigned conflict;};
Result run(Case const& c,array<Row,2> const& actions){
 int q=START,h=c.h;auto tape=c.initial;unsigned read=0;
 int cq=q,ch=h,power=1,period=0;auto checkpoint=tape;
 for(int step=0;step<10000;step++){
  if(q==96&&h==c.oh)for(auto const& t:c.target)if(tape==t)return{0,-1,step,read};
  if(q==254||h<0||h>=WIDTH||q<0||q>NEW)return{1,-1,step,read};
  int b=tape[h];Row a=table[q][b];
  if(q==NEW){read|=(1u<<b);a=actions[b];if(a.t<0)return{2,b,step,read};}
  if(a.t<0)return{1,-1,step,read};
  tape[h]=a.w;h+=a.d;q=a.t;
  period++;
  if(q==cq&&h==ch&&tape==checkpoint)return{1,-1,step+1,read};
  if(period==power){cq=q;ch=h;checkpoint=tape;power*=2;period=0;}
 }
 return{1,-1,10000,read};
}
int main(int argc,char**argv){
 if(argc<2||argc>3){cerr<<"usage: zero_newstate DIRECTORY [ENTRY_STATE]\n";return 2;}
 if(argc==3)START=stoi(argv[2]);assert(START==0||START==75||START==109);
 string dir=argv[1],line;ifstream tf(dir+"/table.tm");
 while(getline(tf,line)){
  if(line.empty()||line[0]=='#')continue;
  istringstream ss(line);int q,b,w,t;char d;ss>>q>>b>>w>>d>>t;
  table[q][b]={w,d=='R'?1:-1,t};
 }
 ifstream cf(dir+"/cases.txt");Case c;int n;array<int,3> m;
 while(cf>>c.id>>c.r>>c.h>>c.oh>>n>>m[0]>>m[1]>>m[2]){
  c.h+=OFFSET+(START==75);c.oh+=OFFSET;c.initial.reset();for(auto&t:c.target)t.reset();int x;
  for(int i=0;i<n;i++){cf>>x;c.initial[x+OFFSET]=true;}
  for(int j=0;j<3;j++)for(int i=0;i<m[j];i++){cf>>x;c.target[j][x+OFFSET]=true;}
  cases.push_back(c);
 }
 assert(cases.size()==(START==109?81:27));
 auto candidate_table=table;
 ifstream control(dir+"/control.tm");assert(control);
 while(getline(control,line)){
  if(line.empty()||line[0]=='#')continue;
  istringstream ss(line);int q,b,w,t;char d;ss>>q>>b>>w>>d>>t;
  table[q][b]={w,d=='R'?1:-1,t};
 }
 array<Row,2> unused;
 int control_checks=0;
 for(auto const& sample:cases)if(START!=109||sample.id>=27){assert(run(sample,unused).kind==0);control_checks++;}
 table=candidate_table;
 cout<<"CONTROL "<<control_checks<<" exact original continuation samples passed\n"<<flush;
 vector<int> states;for(int q=0;q<254;q++)if(table[q][0].t>=0)states.push_back(q);
 assert(states.size()==250);states.push_back(NEW);
 vector<int> targets=states;targets.push_back(254);
 long long nodes=0,checks=0,pruned=0,survivors=0,backjumps=0;
 auto started=chrono::steady_clock::now();ofstream results(dir+"/search.jsonl");
 for(int incoming_w=0;incoming_w<2;incoming_w++)for(int incoming_d:{-1,1}){
  if(START==109&&(incoming_w!=0||incoming_d!=1))continue;
  table[START][0]={incoming_w,incoming_d,NEW};array<Row,2> actions;
  long long family_nodes=0,family_checks=0,family_survivors=0;
  auto descend=[&](auto&& self)->unsigned{
   nodes++;family_nodes++;
   for(Case const& c:cases){
    auto r=run(c,actions);checks++;family_checks++;
    if(r.kind==1){pruned++;return r.conflict;}
    if(r.kind==2){
     int j=r.index;unsigned conflict_union=0;
     for(int w=0;w<2;w++)for(int d:{-1,1})for(int t:targets){
      actions[j]={w,d,t};unsigned conflict=self(self);actions[j]=Row{};
      if(!(conflict&(1u<<j))){backjumps++;return conflict;}
      conflict_union|=(conflict&~(1u<<j));
     }
     return conflict_union;
    }
   }
   survivors++;family_survivors++;
   string stem="candidate_"+to_string(incoming_w)+(incoming_d<0?"L":"R")+"_"+to_string(family_survivors);
   ofstream out(dir+"/"+stem+".tm");out<<"#! start 64\n";
   for(int q:states)for(int b=0;b<2;b++){
    Row a=q==NEW?actions[b]:table[q][b];if(a.t<0)a={0,-1,254};
    assert(a.t>=0);out<<q<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.t<<'\n';
   }
   cout<<"SURVIVOR "<<stem<<'\n'<<flush;
   return 3;
  };
  descend(descend);
  results<<"{\"incoming_write\":"<<incoming_w<<",\"incoming_move\":\""<<(incoming_d<0?'L':'R')<<"\",\"nodes\":"<<family_nodes<<",\"checks\":"<<family_checks<<",\"survivors\":"<<family_survivors<<"}\n"<<flush;
  cout<<"DONE "<<incoming_w<<(incoming_d<0?'L':'R')<<" nodes="<<family_nodes<<" checks="<<family_checks<<" survivors="<<family_survivors<<'\n'<<flush;
 }
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-started).count();
 ofstream summary(dir+"/summary.json");summary<<"{\"entry_state\":"<<START<<",\"samples\":"<<cases.size()<<",\"full_action_recipes\":"<<(START==109?1016064:4064256)<<",\"search_nodes\":"<<nodes<<",\"checks\":"<<checks<<",\"survivors\":"<<survivors<<",\"backjumps\":"<<backjumps<<",\"seconds\":"<<seconds<<"}\n";
}
