#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <chrono>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using cpp_int=unsigned __int128;
std::ostream& operator<<(std::ostream& out,cpp_int n){std::string s;do{s.push_back(char('0'+n%10));n/=10;}while(n);std::reverse(s.begin(),s.end());return out<<s;}
using namespace std;

struct Row { int w=-1,d=0,t=-1; bool operator==(Row const&)const=default; };
struct Seg { int k,b,a,c; bool operator==(Seg const&)const=default; };
Seg bit(int b){return {0,b,0,1};}
Seg runseg(int b,int a,int c){return {1,b,a,c};}
Seg box(int phase,int effect,int r){return {2,phase,effect,r};}
using Tape=deque<Seg>;
using Canon=vector<Seg>;
array<array<Row,2>,255> original;
struct Case {int id;string pc;int branch,zero;string next;int overflow,effect,reg,halt,cost;Canon right;};
vector<Case> cases;
array<int,255> skip;
int totalChecks=0;

Canon canon(Tape const& side,bool left){
 Canon out;
 for(Seg s:side){
  if(s.k==2){out.push_back(s);continue;}
  if(s.k==0)s={1,s.b,0,1};
  if(s.a<0||s.c<0)throw 1;
  if(s.a==0&&s.c==0)continue;
  if(!out.empty()&&out.back().k!=2&&out.back().b==s.b){out.back().a+=s.a;out.back().c+=s.c;}
  else out.push_back(s);
 }
 if(left)while(!out.empty()&&out.back().k!=2&&out.back().b==0)out.pop_back();
 return out;
}

struct Result { int outcome, cost, missing; }; // 0 success, 1 fuel,2 unsupported,3 missing,4 branch
Result execute(Case const& cs,int dead,array<int,510> const& incoming_map,vector<Row> const& actions,
               bitset<510>* used=nullptr){
 int q=96,literals=0,rules=0;
 bool onleft=false;
 Tape left={bit(1)},right;
 for(char c:cs.pc)right.push_back(bit(c-'0'));
 right.push_back(runseg(0,1,43-int(cs.pc.size())));
 right.push_back(bit(1));right.push_back(box(0,-1,-1));
 int request=-1;
 auto row=[&](int s,int b)->Row {
  int key=2*s+b;
  if(used)(*used)[key]=true;
  int index=incoming_map[key];
  if(index>=0){if(actions[index].t<0)request=index;return actions[index];}
  if(s==dead)return Row{};
  return original[s][b];
 };
 for(int fuel=0;fuel<1000;fuel++){
  if(literals>0){
   if(cs.halt&&q==254)return{0,rules,-1};
   if(!cs.halt&&!onleft&&q==96&&canon(left,true)==Canon{runseg(1,0,1)}&&canon(right,false)==cs.right)return{0,rules,-1};
  }
  if(onleft){
   if(left.empty()){right.push_front(bit(0));onleft=false;rules++;continue;}
   Seg s=left.front();
   if(s.k==0){left.pop_front();right.push_front(s);onleft=false;rules++;continue;}
   if(s.k!=1)return{2,rules,-1};
   Row a=row(q,s.b);if(request>=0)return{4,rules,request};if(a.t<0)return{3,rules,-1};
   if(a.d==-1&&a.t==q){left.pop_front();right.push_front(runseg(a.w,s.a,s.c));rules++;continue;}
   if(s.c>0){left.front().c--;left.push_front(bit(s.b));rules++;continue;}
   if(s.a==0){left.pop_front();rules++;continue;}
   return{2,rules,-1};
  }
  if(right.empty())return{2,rules,-1};
  Seg s=right.front();
  if(s.k==0){
   Row a=row(q,s.b);if(request>=0)return{4,rules,request};if(a.t<0)return{3,rules,-1};
   q=a.t;literals++;rules++;
   if(a.d==1){left.push_front(bit(a.w));right.pop_front();}
   else{right.front()=bit(a.w);onleft=true;}
   continue;
  }
  if(s.k==1){
   Row a=row(q,s.b);if(request>=0)return{4,rules,request};if(a.t<0)return{3,rules,-1};
   if(a.d==1&&a.t==q){left.push_front(runseg(a.w,s.a,s.c));right.pop_front();rules++;continue;}
   if(s.c>0){right.front().c--;right.push_front(bit(s.b));rules++;continue;}
   if(s.a==0){right.pop_front();rules++;continue;}
   return{2,rules,-1};
  }
  if(s.k!=2||right.size()!=1)return{2,rules,-1};
  if(s.b==0&&s.a==-1&&skip[q]>=0){int r=skip[q];q=(r==0?2:6);right.front()=box(1,-1,r);onleft=true;rules++;continue;}
  if(s.b==1&&s.c>=0&&s.c<9){
   if(q==73){q=48;right.front()=box(0,0,s.c);onleft=true;rules++;continue;}
   if(q==43&&cs.branch==s.c){
    if(cs.zero){q=3;right.front()=box(0,-1,-1);}
    else{q=(s.c==0?63:48);right.front()=box(0,1,s.c);}
    onleft=true;rules++;continue;
   }
  }
  Row a=row(q,0);if(request>=0)return{4,rules,request};if(a.t<0)return{3,rules,-1};
  if(a.w!=0||a.d!=-1)return{2,rules,-1};
  q=a.t;onleft=true;literals++;rules++;
 }
 return{1,rules,-1};
}

struct Assignment { vector<Row> rows; int defined; };
int main(int argc,char**argv){
 if(argc<2){cerr<<"directory required\n";return 2;}
 string dir=argv[1];

 for(auto& a:original)for(auto& r:a)r=Row{};
 skip.fill(-1);int sk[]={60,44,31,56,38,40,28,64,69};for(int i=0;i<9;i++)skip[sk[i]]=i;
 ifstream tf(dir+"/native_table.txt");int q,b,w,t;char d;
 while(tf>>q>>b>>w>>d>>t)original[q][b]={w,d=='R'?1:-1,t};
 ifstream cf(dir+"/native_cases.txt");Case c;
 while(cf>>c.id>>c.pc>>c.branch>>c.zero>>c.next>>c.overflow>>c.effect>>c.reg>>c.halt>>c.cost){
  Tape right;
  if(c.next!="-")for(char x:c.next)right.push_back(bit(x-'0'));
  right.push_back(runseg(0,1,(c.overflow?44:43)-(c.next=="-"?0:int(c.next.size()))));
  right.push_back(bit(1));right.push_back(box(0,c.effect,c.reg));c.right=canon(right,false);
  cases.push_back(c);
 }
 assert(!cases.empty());
 vector<bitset<510>> usage(cases.size());
 vector<Row> missing;
 array<int,510> no_incoming;no_incoming.fill(-1);
 for(int i=0;i<int(cases.size());i++){
  Result a=execute(cases[i],-1,no_incoming,missing,&usage[i]);
  if(a.outcome!=0||a.cost!=cases[i].cost){cerr<<"BASELINE DIFFERENCE "<<cases[i].id<<' '<<a.outcome<<' '<<a.cost<<' '<<cases[i].cost<<'\n';return 1;}
 }
 // Compare every observed lookup with the independently generated Python sets.
 ifstream uf(dir+"/native_usage.txt");string line;
 array<set<int>,510> wanted;
 while(getline(uf,line)){
  istringstream ss(line);string list;ss>>q>>b>>list;replace(list.begin(),list.end(),',',' ');istringstream ls(list);int i;while(ls>>i)wanted[2*q+b].insert(i);
 }
 for(int i=0;i<int(cases.size());i++)for(int row=0;row<510;row++)assert(usage[i][row]==wanted[row].count(cases[i].id));
 cout<<"BASELINE passed; all rule costs and table lookup sets match Python\n"<<flush;
 set<int> protect;
 int ps[]={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131};
 for(int q:ps)for(int b=0;b<2;b++)if(!(q==3&&b==0))protect.insert(2*q+b);
 set<int> protected_targets;for(int k:protect)protected_targets.insert(original[k/2][k%2].t);
 vector<int> states,family;map<int,vector<int>> incoming;
 for(int q=0;q<254;q++)if(original[q][0].t>=0)states.push_back(q);
 for(int q:states){
  if(q==64||q==96||protected_targets.count(q)||protect.count(2*q)||protect.count(2*q+1))continue;
  for(int s:states)for(int b=0;b<2;b++)if(s!=q&&original[s][b].t==q)incoming[q].push_back(2*s+b);
  if(!incoming[q].empty())family.push_back(q);
 }
 assert(!family.empty());
 sort(family.begin(),family.end(),[&](int a,int b){return pair(incoming[a].size(),a)<pair(incoming[b].size(),b);});

 ofstream record(dir+"/local_search.jsonl");
 long long checks=0,tested=0,passed=0;
 auto started=chrono::steady_clock::now();
 map<string,long long> family_tests;
 map<string,map<int,long long>> failures;
 auto certify=[&](int dead,map<int,Row> const& edits,string kind,int target,int copied)->bool {
  array<int,510> incoming_map;incoming_map.fill(-1);vector<Row> actions;
  bitset<510> changed;
  for(auto const&[key,row]:edits){incoming_map[key]=actions.size();actions.push_back(row);changed[key]=true;}
  changed[2*dead]=true;changed[2*dead+1]=true;
  vector<int> affected;
  for(int i=0;i<int(cases.size());i++)if((usage[i]&changed).any())affected.push_back(i);
  sort(affected.begin(),affected.end(),[](int a,int b){return pair(cases[a].cost,cases[a].id)<pair(cases[b].cost,cases[b].id);});
  int fail=-1,reason=0;
  for(int i:affected){Result r=execute(cases[i],dead,incoming_map,actions);checks++;if(r.outcome!=0){fail=cases[i].id;reason=r.outcome;break;}}
  if(fail<0)for(int i=0;i<int(cases.size());i++){Result r=execute(cases[i],dead,incoming_map,actions);checks++;if(r.outcome!=0){fail=cases[i].id;reason=r.outcome;break;}}
  tested++;family_tests[kind]++;
  record<<"{\"family\":\""<<kind<<"\",\"deleted\":"<<dead<<",\"target\":"<<target<<",\"copied_bit\":"<<copied<<",\"failure_case\":"<<fail<<",\"reason\":"<<reason<<"}\n";
  if(fail>=0){failures[kind][fail]++;return false;}
  passed++;
  string stem="local_candidate_"+kind+"_"+to_string(dead)+"_"+to_string(target)+"_"+to_string(copied);
  ofstream out(dir+"/"+stem+".tm");out<<"#! start 64\n";
  for(int q:states)if(q!=dead)for(int b=0;b<2;b++){
   int k=2*q+b;Row row=edits.count(k)?edits.at(k):original[q][b];assert(row.t!=dead);
   out<<q<<' '<<b<<' '<<row.w<<' '<<(row.d==1?'R':'L')<<' '<<row.t<<'\n';
  }
  cout<<"SURVIVOR "<<stem<<'\n'<<flush;
  return true;
 };
 for(int dead:family)for(int target:states)if(target!=dead){
  map<int,Row> edits;
  for(int key:incoming[dead]){Row row=original[key/2][key%2];row.t=target;edits[key]=row;}
  certify(dead,edits,"uniform",target,-1);
 }
 cout<<"UNIFORM complete "<<tested<<" survivors="<<passed<<'\n'<<flush;
 for(int dead:family)for(int target:states)if(target!=dead)for(int bit=0;bit<2;bit++){
  int copied_key=2*target+bit;
  if(protect.count(copied_key))continue;
  map<int,Row> edits;
  for(int key:incoming[dead]){Row row=original[key/2][key%2];row.t=target;edits[key]=row;}
  Row copied=original[dead][bit];if(copied.t==dead)copied.t=target;
  Row existing=edits.count(copied_key)?edits[copied_key]:original[target][bit];
  if(copied==existing)continue;
  edits[copied_key]=copied;
  certify(dead,edits,"mixed",target,bit);
 }
 double elapsed=chrono::duration<double>(chrono::steady_clock::now()-started).count();
 ofstream out(dir+"/local_search_summary.json");
 out<<"{\"baseline_cases\":"<<cases.size()<<",\"baseline_rule_costs_and_usage_match_python\":true,\"tested\":"<<tested<<",\"checks\":"<<checks<<",\"survivors\":"<<passed<<",\"uniform\":"<<family_tests["uniform"]<<",\"mixed\":"<<family_tests["mixed"]<<",\"seconds\":"<<elapsed<<"}\n";
 cout<<"ALL complete tested="<<tested<<" checks="<<checks<<" survivors="<<passed<<" seconds="<<elapsed<<'\n';
}
