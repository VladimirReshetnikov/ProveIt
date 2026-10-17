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
int totalChecks=0; bool reuse_mode=false;

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
  if(s.b==0&&s.a==-1&&skip[q]>=0){int r=skip[q];q=(reuse_mode?6:(r==0?2:6));right.front()=box(1,-1,r);onleft=true;rules++;continue;}
  if(s.b==1&&s.c>=0&&s.c<9){
   if(q==73){q=48;right.front()=box(0,0,s.c);onleft=true;rules++;continue;}
   if(q==43&&cs.branch==s.c){
    if(cs.zero){q=3;right.front()=box(0,-1,-1);}
    else{Canon ctx=canon(left,true);if(ctx.size()<2||ctx[0].k==2||ctx[0].b!=1||ctx[0].c<1||ctx[1].k==2||ctx[1].b!=0||ctx[1].c<2)return{2,rules,-1};q=(s.c==0?63:48);right.front()=box(0,1,s.c);left.push_front(bit(1));}
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
 if(argc!=2){cerr<<"usage: native_context_reuse INPUTDIR\n";return 2;}
 string dir=argv[1];
 for(auto& a:original)for(auto& r:a)r=Row{};
 skip.fill(-1);int sk[]={60,44,31,56,38,40,28,64,69};for(int i=0;i<9;i++)skip[sk[i]]=i;
 ifstream tf(dir+"/native_table.txt");int q,b,w,t;char d;
 while(tf>>q>>b>>w>>d>>t)original[q][b]={w,d=='R'?1:-1,t};
 ifstream cf(dir+"/native_cases.txt");Case c;
 while(cf>>c.id>>c.pc>>c.branch>>c.zero>>c.next>>c.overflow>>c.effect>>c.reg>>c.halt>>c.cost){
  Tape right;if(c.next!="-")for(char x:c.next)right.push_back(bit(x-'0'));
  right.push_back(runseg(0,1,43+c.overflow+(c.effect==1)-(c.next=="-"?0:int(c.next.size()))));
  right.push_back(bit(1));right.push_back(box(0,c.effect,c.reg));c.right=canon(right,false);cases.push_back(c);
 }
 assert(cases.size()==8366);array<int,510> no_incoming;no_incoming.fill(-1);
 for(auto const& c:cases){auto r=execute(c,-1,no_incoming,{});assert(r.outcome==0&&r.cost==c.cost);}
 cout<<"BASELINE all8366 costs match Python\n"<<flush;
 // A new mark contract: physical0 now exits at6 on the header1; other registers
 // still exit6. The next step at6/1 equals the former step at2/1.
 reuse_mode=true;
 original[75][1]={1,-1,2};original[2][1]={1,-1,97};original[0][1]={0,-1,4};original[42][1]={1,-1,6};
 vector<int> states;for(int q=0;q<254;q++)if(q!=85&&original[q][0].t>=0)states.push_back(q);
 vector<int> keys={40,41,287}; // (20,0),(20,1),(143,1)
 array<int,510> incoming_map;incoming_map.fill(-1);for(int i=0;i<int(keys.size());i++)incoming_map[keys[i]]=i;
 vector<Row> actions(keys.size());sort(cases.begin(),cases.end(),[](Case const&a,Case const&b){return pair(a.cost,a.id)<pair(b.cost,b.id);});
 long long nodes=0,checks=0,backjumps=0;bool found=false,capped=false;map<int,long long> failures;auto begun=chrono::steady_clock::now();
 auto dfs=[&](auto&& self)->unsigned{
  nodes++;if(nodes>20000000){capped=true;return 0xffffffffu;}
  for(size_t ci=0;ci<cases.size();ci++){
   auto const& c=cases[ci];bitset<510> used;auto r=execute(c,85,incoming_map,actions,&used);checks++;
   unsigned conflict=0;for(int j=0;j<int(keys.size());j++)if(used[keys[j]])conflict|=1u<<j;
   if(r.outcome!=0&&r.outcome!=4){failures[c.id]++;if(ci>0)swap(cases[0],cases[ci]);return conflict;}
   if(r.outcome==4){
    int j=r.missing;unsigned joined=0;
    for(int w=0;w<2;w++)for(int d:{-1,1})for(int t=0;t<=254;t++)if(t!=85&&(t==254||original[t][0].t>=0)){
     actions[j]={w,d,t};unsigned answer=self(self);if(found)return answer;actions[j]=Row{};
     if(capped)return answer;
     if(!(answer&(1u<<j))){backjumps++;return answer;}
     joined|=answer&~(1u<<j);
    }
    return joined;
   }
  }
  found=true;ofstream out(dir+"/context_reuse251.tm");out<<"#! start 64\n";
  for(int q:states)for(int b=0;b<2;b++){int j=incoming_map[2*q+b];Row a=j<0?original[q][b]:actions[j];if(a.t<0){a=original[q][b];a.t=254;}assert(a.t!=85);out<<q<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.t<<'\n';}
  return 0xffffffffu;
 };
 dfs(dfs);
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-begun).count();
 ofstream out(dir+"/context_reuse_adaptive_summary.json");out<<"{\"baseline_guards\":8366,\"nodes\":"<<nodes<<",\"checks\":"<<checks<<",\"backjumps\":"<<backjumps<<",\"found\":"<<(found?"true":"false")<<",\"capped\":"<<(capped?"true":"false")<<",\"seconds\":"<<seconds<<",\"failures\":{";
 bool comma=false;for(auto [id,count]:failures){if(comma)out<<',';comma=true;out<<'\"'<<id<<"\":"<<count;}out<<"}}\n";
 cout<<"DONE found="<<found<<" capped="<<capped<<" nodes="<<nodes<<" checks="<<checks<<" seconds="<<seconds<<'\n';
}
