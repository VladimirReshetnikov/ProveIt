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
Result execute(Case const& cs,int dead,int in0,int in1,array<Row,2> const& actions,
               bitset<510>* used=nullptr){
 int q=96,literals=0,rules=0;
 bool onleft=false;
 Tape left={bit(1)},right;
 for(char c:cs.pc)right.push_back(bit(c-'0'));
 right.push_back(runseg(0,1,40-int(cs.pc.size())));
 right.push_back(bit(1));right.push_back(box(0,-1,-1));
 int request=-1;
 auto row=[&](int s,int b)->Row {
  int key=2*s+b;
  if(used)(*used)[key]=true;
  if(key==in0){if(actions[0].t<0)request=0;return actions[0];}
  if(key==in1){if(actions[1].t<0)request=1;return actions[1];}
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

struct Assignment { array<Row,2> rows; int defined; };
int main(int argc,char**argv){
 if(argc<2){cerr<<"directory required\n";return 2;}
 string dir=argv[1];
 for(auto& a:original)for(auto& r:a)r=Row{};
 skip.fill(-1);int sk[]={60,44,31,56,38,40,28,64,69};for(int i=0;i<9;i++)skip[sk[i]]=i;
 ifstream tf(argc>2?argv[2]:dir+"/native_table.txt");int q,b,w,t;char d;
 string table_line;
 while(getline(tf,table_line)){if(table_line.empty()||table_line[0]=='#')continue;istringstream row(table_line);row>>q>>b>>w>>d>>t;assert(row&&q>=0&&q<254&&b>=0&&b<2&&w>=0&&w<2&&(d=='R'||d=='L')&&t>=0&&t<=254);original[q][b]={w,d=='R'?1:-1,t};}
 ifstream cf(dir+"/native_cases.txt");Case c;
 while(cf>>c.id>>c.pc>>c.branch>>c.zero>>c.next>>c.overflow>>c.effect>>c.reg>>c.halt>>c.cost){
  Tape right;
  if(c.next!="-")for(char x:c.next)right.push_back(bit(x-'0'));
  right.push_back(runseg(0,1,(c.overflow?41:40)-(c.next=="-"?0:int(c.next.size()))));
  right.push_back(bit(1));right.push_back(box(0,c.effect,c.reg));c.right=canon(right,false);
  cases.push_back(c);
 }
 assert(!cases.empty());
 vector<bitset<510>> usage(cases.size());
 array<Row,2> missing={Row{},Row{}};
 for(int i=0;i<int(cases.size());i++){
  Result a=execute(cases[i],-1,-1,-1,missing,&usage[i]);
  if(a.outcome!=0){cout<<"{\"passed\":false,\"checked\":"<<i+1<<",\"failure_case\":"<<cases[i].id<<",\"outcome\":"<<a.outcome<<",\"rules\":"<<a.cost<<"}\n";return 1;}
 }
 cout<<"{\"passed\":true,\"checked\":"<<cases.size()<<"}\n";
}
