// Finite candidate discovery only. No bounded failure proves inequivalence.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
constexpr int OFFSET=1024, WIDTH=8192, MAXQ=512;
struct Action{int w=-1,d=0,z=-1;bool operator==(const Action&a)const{return w==a.w&&d==a.d&&z==a.z;}};
using Table=array<Action,MAXQ*2>;
struct Tape{
 bitset<WIDTH> bits;int lo=WIDTH-OFFSET,hi=-OFFSET-1;
 bool read(int h)const{return bits[h+OFFSET];}
 void write(int h,int v){bits[h+OFFSET]=v;if(v){lo=min(lo,h);hi=max(hi,h);}else if(lo<=hi){if(h==lo){while(lo<=hi&&!read(lo))lo++;}if(h==hi){while(hi>=lo&&!read(hi))hi--;}}}
 bool operator==(const Tape&t)const{return bits==t.bits;}
};
struct Case{int ordinal,positive,trial,targetq,targeth;Tape input,target;vector<int>used;long steps=0;};
struct Result{int status,q,h;long steps;Tape tape;vector<int>used;};
Table load_table(string file,vector<int>&states){
 Table t;ifstream f(file);string l;
 while(getline(f,l))if(l.size()&&l[0]!='#'){
  istringstream s(l);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;
  if(!s||q<0||q>=MAXQ||b<0||b>1||w<0||w>1||(d!='L'&&d!='R'))throw runtime_error("Bad table");
  t[2*q+b]={w,d=='R'?1:-1,z};if(!b)states.push_back(q);
 }
 return t;
}
vector<Case> load_cases(string file){
 ifstream f(file);int n;f>>n;vector<Case>cases;
 for(int k=0;k<n;k++){
  Case c;int count,x;f>>c.ordinal>>c.positive>>c.trial>>count;
  for(int j=0;j<count;j++){f>>x;c.input.write(x,1);}
  f>>c.targetq>>c.targeth>>count;
  for(int j=0;j<count;j++){f>>x;c.target.write(x,1);}
  if(!f)throw runtime_error("Bad case");cases.push_back(c);
 }
 return cases;
}
bool clean(int h,const Tape&t){
 if(t.lo!=h-1)return false;
 int header=h+52;while(header<=t.hi&&!t.read(header))header++;
 if(header>t.hi||header<h+64)return false;
 int p=header+1,count=0;
 while(p<=t.hi){if(t.read(p)||!t.read(p+1))return false;p++;while(p<=t.hi&&t.read(p))p++;count++;}
 return count>=10;
}
Result simulate(const Table&t,const Case&c,int cap=20000,bool record=false){
 Tape tape=c.input;int q=84,h=0;bitset<MAXQ*2> seen;
 for(int k=0;k<=cap;k++){
  if(q==254)return {c.targetq==254?0:1,q,h,k,tape,{}};
  if(k&&q==84){
   if(c.targetq==84&&h==c.targeth&&tape==c.target){vector<int>u;if(record)for(int i=0;i<MAXQ*2;i++)if(seen[i])u.push_back(i);return {0,q,h,k,tape,u};}
   if(clean(h,tape))return {1,q,h,k,tape,{}};
  }
  if(k==cap)return {2,q,h,k,tape,{}};
  if(h<-OFFSET+2||h>=WIDTH-OFFSET-2)return {3,q,h,k,tape,{}};
  int b=tape.read(h),key=q*2+b;Action a=t[key];if(a.w<0)return {4,q,h,k,tape,{}};
  if(record)seen[key]=true;
  if(!b&&a.z==q&&((a.d==1&&h>=tape.hi)||(a.d==-1&&h<=tape.lo)))return {5,q,h,k,tape,{}};
  tape.write(h,a.w);h+=a.d;q=a.z;
 }
 throw runtime_error("unreachable");
}
vector<long> parse_root(int h,const Tape&t){
 if(t.lo!=h-1)return{};
 int header=h;while(header<=t.hi&&!t.read(header))header++;
 if(header<h+64||header>t.hi)return{};
 int p=header+1;vector<long>vals;
 while(p<=t.hi){if(t.read(p)||!t.read(p+1))return{};p++;int n=0;while(p<=t.hi&&t.read(p)){p++;n++;}vals.push_back(n-1);}
 if(vals.size()<10)return{};
 int phy[]={6,2,0,4,3,7,8,5,1};vector<long>result={header-h-64};for(int x:phy)result.push_back(vals[x]);result.insert(result.end(),vals.begin()+9,vals.end());return result;
}
Result bootstrap(const Table&t,int start,int cap=1000000,bool record=false){
 Tape tape;int q=start,h=0;bitset<MAXQ*2> seen;
 for(int k=0;k<=cap;k++){
  if(q==254)return {1,q,h,k,tape,{}};
  if(q==84&&!parse_root(h,tape).empty())return {0,q,h,k,tape,{}};
  if(k==cap)return {2,q,h,k,tape,{}};
  if(h<-OFFSET+2||h>=WIDTH-OFFSET-2)return {3,q,h,k,tape,{}};
  int b=tape.read(h),key=2*q+b;Action a=t[key];if(a.w<0)return {4,q,h,k,tape,{}};
  if(record)seen[key]=true;
  if(!b&&a.z==q&&((a.d==1&&h>=tape.hi)||(a.d==-1&&h<=tape.lo))){vector<int>u;if(record)for(int i=0;i<MAXQ*2;i++)if(seen[i])u.push_back(i);return {5,q,h,k,tape,u};}
  tape.write(h,a.w);h+=a.d;q=a.z;
 }
 throw runtime_error("unreachable");
}
void dump_array(const vector<long>&a){cout<<'[';for(size_t i=0;i<a.size();i++){if(i)cout<<',';cout<<a[i];}cout<<']';}
void dump_support(const Tape&t){cout<<'[';bool first=true;for(int i=t.lo;i<=t.hi;i++)if(t.read(i)){if(!first)cout<<',';cout<<i;first=false;}cout<<']';}
