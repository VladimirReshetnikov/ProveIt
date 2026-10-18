// Bounded exhaustive synthesis of two existing rows in the rejected 250-state
// shared-scanner table.  No new state is allocated.
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
constexpr int WIDTH=2048, OFFSET=512;
int START=0;
struct Row{int w=-1,d=0,t=-1;};
struct Case{int id,r,h,oh;bitset<WIDTH> initial;array<bitset<WIDTH>,3> target;};
array<array<Row,2>,256> table;
vector<Case> cases;
struct Result{int kind,index,cost;unsigned conflict;};
int variable(int q,int b){
 if(q==START&&b==0)return 0;
 if(q==131&&b==1)return 1;
 return -1;
}
Result run(Case const& c,array<Row,2> const& actions,bool synthesize=true){
 int q=START,h=c.h;auto tape=c.initial;unsigned read=0;
 int cq=q,ch=h,power=1,period=0;auto checkpoint=tape;
 for(int step=0;step<10000;step++){
  if(q==96&&h==c.oh)for(auto const& t:c.target)if(tape==t)return{0,-1,step,read};
  if(q==254||h<0||h>=WIDTH||q<0||q>=254)return{1,-1,step,read};
  int b=tape[h];Row a=table[q][b];
  int j=synthesize?variable(q,b):-1;
  if(j>=0){read|=(1u<<j);a=actions[j];if(a.t<0)return{2,j,step,read};}
  if(a.t<0)return{1,-1,step,read};
  tape[h]=a.w;h+=a.d;q=a.t;
  period++;
  if(q==cq&&h==ch&&tape==checkpoint)return{1,-1,step+1,read};
  if(period==power){cq=q;ch=h;checkpoint=tape;power*=2;period=0;}
 }
 return{1,-1,10000,read};
}
int main(int argc,char**argv){
 if(argc!=4){cerr<<"usage: zero_existing_pair INPUT_DIRECTORY OUTPUT_DIRECTORY ENTRY_STATE\n";return 2;}
 string input=argv[1],dir=argv[2],line;START=stoi(argv[3]);assert(START==0||START==75);
 ifstream tf(input+"/table.tm");assert(tf);
 while(getline(tf,line)){
  if(line.empty()||line[0]=='#')continue;
  istringstream ss(line);int q,b,w,t;char d;ss>>q>>b>>w>>d>>t;
  table[q][b]={w,d=='R'?1:-1,t};
 }
 assert(table[131][0].w==0&&table[131][0].d==1&&table[131][0].t==95);
 ifstream cf(input+"/cases.txt");assert(cf);Case c;int n;array<int,3> m;
 while(cf>>c.id>>c.r>>c.h>>c.oh>>n>>m[0]>>m[1]>>m[2]){
  c.h+=OFFSET+(START==75);c.oh+=OFFSET;c.initial.reset();for(auto&t:c.target)t.reset();int x;
  for(int i=0;i<n;i++){cf>>x;c.initial[x+OFFSET]=true;}
  for(int j=0;j<3;j++)for(int i=0;i<m[j];i++){cf>>x;c.target[j][x+OFFSET]=true;}
  cases.push_back(c);
 }
 assert(cases.size()==27);
 auto candidate_table=table;
 ifstream control(input+"/control.tm");assert(control);
 while(getline(control,line)){
  if(line.empty()||line[0]=='#')continue;
  istringstream ss(line);int q,b,w,t;char d;ss>>q>>b>>w>>d>>t;
  table[q][b]={w,d=='R'?1:-1,t};
 }
 array<Row,2> actions;
 for(auto const& sample:cases)assert(run(sample,actions,false).kind==0);
 table=candidate_table;
 cout<<"CONTROL 27 exact original continuation samples passed\n"<<flush;
 vector<int> states;for(int q=0;q<254;q++)if(table[q][0].t>=0)states.push_back(q);
 assert(states.size()==250);
 vector<int> targets=states;targets.push_back(254);
 long long nodes=0,checks=0,pruned=0,survivors=0,backjumps=0;
 auto started=chrono::steady_clock::now();ofstream results(dir+"/survivors.jsonl");assert(results);
 auto descend=[&](auto&& self)->unsigned{
  nodes++;
  for(Case const& c:cases){
   auto r=run(c,actions);checks++;
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
  survivors++;
  string stem="candidate_"+to_string(survivors);
  ofstream out(dir+"/"+stem+".tm");out<<"#! start 64\n";
  for(int q:states)for(int b=0;b<2;b++){
   int j=variable(q,b);Row a=j>=0?actions[j]:table[q][b];
   if(a.t<0)a=table[q][b];
   assert(a.t>=0);out<<q<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.t<<'\n';
  }
  results<<"{\"candidate\":\""<<stem<<"\",\"entry_action\":["<<actions[0].w<<','<<actions[0].d<<','<<actions[0].t<<"],\"131_read1_action\":["<<actions[1].w<<','<<actions[1].d<<','<<actions[1].t<<"]}\n"<<flush;
  cout<<"SURVIVOR "<<stem<<'\n'<<flush;
  return 3;
 };
 descend(descend);
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-started).count();
 ofstream summary(dir+"/summary.json");assert(summary);
 summary<<"{\"entry_state\":"<<START<<",\"other_free_row\":[131,1],\"fixed_row\":[131,0,0,1,95],\"working_states\":250,\"samples\":"<<cases.size()<<",\"step_bound\":10000,\"full_action_recipes\":1008016,\"search_nodes\":"<<nodes<<",\"checks\":"<<checks<<",\"survivors\":"<<survivors<<",\"backjumps\":"<<backjumps<<",\"seconds\":"<<seconds<<"}\n";
 cout<<"DONE entry="<<START<<" nodes="<<nodes<<" checks="<<checks<<" survivors="<<survivors<<" seconds="<<seconds<<'\n'<<flush;
}
