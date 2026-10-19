// Discovery acceleration for the inherited prefix_affine.py sufficient oracle.
// A positive answer is to be replayed by that original Python verifier.
#include <algorithm>
#include <array>
#include <cstdint>
#include <deque>
#include <string>
#include <vector>

struct Action {int write,move,next;};
struct Site {uint64_t bits;int length,op,reg;};
// Seg type 0: literal; 1: affine run; 2: register box.
struct Seg {int type,b,a,c,kind,r;};
using Tape=std::deque<Seg>;
static Seg bit(int b){return {0,b,0,1,0,-1};}
static Seg run(int b,int a,int c){return {1,b,a,c,0,-1};}
static Seg box(int kind=0,int r=-1){return {2,0,0,0,kind,r};}
static bool equal(const Seg&x,const Seg&y){return x.type==y.type&&x.b==y.b&&x.a==y.a&&x.c==y.c&&x.kind==y.kind&&x.r==y.r;}
static std::vector<Seg> canon(const Tape&t,bool left){
 std::vector<Seg> v;
 for(auto s:t){
  if(s.type==2){v.push_back(s);continue;}
  if(s.type==0)s=run(s.b,0,1);
  if(s.a==0&&s.c==0)continue;
  if(!v.empty()&&v.back().type==1&&v.back().b==s.b){v.back().a+=s.a;v.back().c+=s.c;}
  else v.push_back(s);
 }
 if(left)while(!v.empty()&&v.back().type==1&&v.back().b==0)v.pop_back();
 return v;
}
static bool same(const Tape&t,bool left,const std::vector<Seg>&goal){
 auto a=canon(t,left);if(a.size()!=goal.size())return false;
 for(unsigned i=0;i<a.size();i++)if(!equal(a[i],goal[i]))return false;
 return true;
}
static std::string path(const Site&s){std::string p;for(int i=s.length-1;i>=0;i--)p.push_back('0'+((s.bits>>i)&1));return p;}
static std::string strip(std::string p,char bit,int k){
 while(k--){auto pos=p.rfind(bit);if(pos==std::string::npos)return "";p.resize(pos);}
 return p;
}
static std::string inc(std::string p,int&over){
 over=1;
 for(int i=int(p.size())-1;i>=0&&over;i--){if(p[i]=='0'){p[i]='1';over=0;}else p[i]='0';}
 return p;
}
static int marked(int q){
 switch(q){case 60:return 0;case 44:return 1;case 31:return 2;case 56:return 3;case 38:return 4;case 40:return 5;case 28:return 6;case 64:return 7;case 69:return 8;default:return -1;}
}
static int execute(const Action* table,int maxq,const Site&s,int branch,std::array<bool,2048>&used,int fuel){
 auto pc=path(s),succ=pc;int extra=0,over=0,effect=0,er=-1;
 if(s.op=='I'){succ=inc(pc,over);effect=2;er=s.reg;}
 else if(s.op=='D'&&branch==0){succ=inc(pc,over);extra=1;effect=3;er=s.reg;}
 else if(s.op=='D'){succ=inc(strip(pc,'0',1),over);}
 else if(s.op=='B'){succ=inc(strip(pc,'0',s.reg),over);}
 else if(s.op=='C'){succ=strip(pc,'1',s.reg);}
 else if(s.op=='H'){succ="";}
 else return 20;
 if(succ.find('!')!=std::string::npos)return 21;
 Tape left{bit(1)},right;
 for(auto b:pc)right.push_back(bit(b-'0'));
 right.push_back(run(0,1,40-pc.size()));right.push_back(bit(1));right.push_back(box());
 Tape goalr;
 for(auto b:succ)goalr.push_back(bit(b-'0'));
 goalr.push_back(run(0,1,40+extra+over-succ.size()));goalr.push_back(bit(1));goalr.push_back(box(effect,er));
 auto gr=canon(goalr,false),gl=canon(Tape{bit(1)},true);
 int q=96,literal=0;bool onleft=false;
 for(int tick=0;tick<fuel;tick++){
  if(literal>0){if(s.op=='H'&&q==254)return 0;if(s.op!='H'&&!onleft&&q==96&&same(left,true,gl)&&same(right,false,gr))return 0;}
  if(q<0||q>maxq||q==254)return 22;
  if(onleft){
   if(left.empty()){right.push_front(bit(0));onleft=false;continue;}
   auto seg=left.front();
   if(seg.type==0){left.pop_front();right.push_front(seg);onleft=false;continue;}
   if(seg.type!=1)return 23;
   int idx=2*q+seg.b;used[idx]=true;auto a=table[idx];if(a.next<0)return 24;
   if(a.move==-1&&a.next==q){left.pop_front();right.push_front(run(a.write,seg.a,seg.c));continue;}
   if(seg.c>0){left.front().c--;left.push_front(bit(seg.b));continue;}
   if(seg.a==0){left.pop_front();continue;}return 25;
  }
  if(right.empty())return 26;
  auto seg=right.front();
  if(seg.type==0){
   int idx=2*q+seg.b;used[idx]=true;auto a=table[idx];if(a.next<0)return 24;q=a.next;literal++;
   if(a.move==1){left.push_front(bit(a.write));right.pop_front();}
   else{right.front()=bit(a.write);onleft=true;}
   continue;
  }
  if(seg.type==1){
   int idx=2*q+seg.b;used[idx]=true;auto a=table[idx];if(a.next<0)return 24;
   if(a.move==1&&a.next==q){left.push_front(run(a.write,seg.a,seg.c));right.pop_front();continue;}
   if(seg.c>0){right.front().c--;right.push_front(bit(seg.b));continue;}
   if(seg.a==0){right.pop_front();continue;}return 27;
  }
  if(right.size()!=1)return 28;
  int r=marked(q);
  if(seg.kind==0&&r>=0){q=r==0?2:6;right.front()=box(1,r);onleft=true;continue;}
  if(seg.kind==1){
   if(q==73){q=48;right.front()=box(2,seg.r);onleft=true;continue;}
   if(q==95&&s.op=='D'&&s.reg==seg.r){
    if(branch==1){q=112;right.front()=box();}
    else{q=48;right.front()=box(3,seg.r);left.push_front(bit(1));}
    onleft=true;continue;
   }
  }
  int idx=2*q;used[idx]=true;auto a=table[idx];
  if(a.next<0||a.write!=0||a.move!=-1)return 29;
  q=a.next;onleft=true;literal++;
 }
 return 30;
}

extern "C" int affine_cases(const Action* table,int maxq,const Site* sites,int nsites,int* failed_site,int* failed_branch,int* error,unsigned char* rows,int stop_states,int fuel,int* witnesses,int* nwitnesses){
 std::array<bool,2048>used{};
 const int macro[]={2,4,6,20,48,63,73,75,83,95,109,112,131,255,60,44,31,56,38,40,28,64,69};
 for(int q:macro)for(int b=0;b<2;b++)if(!((q==6&&b==0)||(q==20&&b==0)||(q==48&&b==0)||(q==69&&b==1)))used[2*q+b]=true;
 auto finish=[&](){for(int i=0;i<2048;i++)rows[i]=used[i];};
 *nwitnesses=0;int previous_count=0;for(int q=0;q<=maxq;q++)previous_count+=used[2*q]||used[2*q+1];
 for(int i=0;i<nsites;i++){
  for(int b=(sites[i].op=='D'?1:-1);b>=(sites[i].op=='D'?0:-1);b--){
   int result=execute(table,maxq,sites[i],b,used,fuel);
   if(result){*failed_site=i;*failed_branch=b;*error=result;finish();return -1;}
  }
  int count=0;for(int q=0;q<=maxq;q++)count+=used[2*q]||used[2*q+1];
  if(count>previous_count){witnesses[(*nwitnesses)++]=i;previous_count=count;}
  if(stop_states&&count>=stop_states){finish();return 1;}
 }
 finish();return 0;
}
