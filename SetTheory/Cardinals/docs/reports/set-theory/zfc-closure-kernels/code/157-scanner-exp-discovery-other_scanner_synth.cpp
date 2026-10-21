#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <set>
using namespace std;
struct A {int w,d,z; bool operator==(const A&o)const{return w==o.w&&d==o.d&&z==o.z;}};
array<array<A,2>,500> T,base;
vector<int> states;vector<A> acts;
int drop,entry,kth;
vector<int> trace(A initial,int zeros,int patch=-1,A alt={0,0,0},bool check=false){
 array<int,81> tape{},orig{};
 if(zeros>=0)tape[40-zeros-1]=1;
 tape[40+kth]=1;orig=tape;tape[40]=initial.w;
 int q=initial.z,h=initial.d;vector<int> rows;int goalq=zeros<0?84:2,goalh=zeros<0?kth+1:-zeros-2;
 for(int tick=0;tick<240;tick++){
  if(q==goalq&&h==goalh&&tape==orig)return{-1};
  if(h<(zeros<0?-39:-zeros-1)||h>kth||q==drop||q==254||q<0)return rows;
  int b=tape[h+40],row=2*q+b;
  if(!check)rows.push_back(row);
  A a=row==patch?alt:T[q][b];if(!a.d)return rows;
  tape[h+40]=a.w;h+=a.d;q=a.z;
 }
 return rows;
}
bool pass(A a,int row,A b){
 if(trace(a,-1,row,b,true)!=vector<int>{-1})return false;
 for(int m=0;m<=7-kth;m++)if(trace(a,m,row,b,true)!=vector<int>{-1})return false;
 return true;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);string line;set<int>qs;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream s(line);s>>q>>b>>w>>d>>z;base[q][b]={w,d=='R'?1:-1,z};qs.insert(q);}
 int chain[]={2,3,5,9,15,23,34,50};
 for(int index=6;index>=1;index--){
  drop=chain[index];entry=chain[index-1];kth=index;T=base;states.clear();acts.clear();for(int q:qs)if(q!=drop)states.push_back(q);
  for(int q:states)for(int w:{0,1})for(int d:{-1,1})acts.push_back({w,d,q});long tested=0,hits=0;
  for(A a:acts){
   T[entry][0]=a;set<int>choices;
   for(int m=-1;m<=7-kth;m++){auto tr=trace(a,m);for(int r:tr)if(r>=0&&r!=entry*2&&r/2!=drop)choices.insert(r);}
   for(int row:choices)for(A b:acts){if(b==T[row/2][row%2])continue;tested++;if(pass(a,row,b)){
    cout<<"{\"drop\":"<<drop<<",\"entry_state\":"<<entry<<",\"entry\":["<<a.w<<","<<a.d<<","<<a.z<<"],\"patch\":["<<row/2<<","<<row%2<<","<<b.w<<","<<b.d<<","<<b.z<<"]}"<<endl;hits++;
   }}
  }
  cerr<<"drop "<<drop<<" tested "<<tested<<" hits "<<hits<<"\n";
 }
}
