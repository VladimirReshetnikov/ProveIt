#include <array>
#include <vector>
#include <tuple>
#include <fstream>
#include <sstream>
#include <iostream>
#include <set>
using namespace std;
struct A {int w,d,z; bool operator==(const A&o)const{return w==o.w&&d==o.d&&z==o.z;}};
array<array<A,2>,500> T;
vector<int> states;
vector<A> acts;
vector<int> trace(A initial,int input,int patch=-1,A alt={0,0,0},bool check=false){
 array<int,9> tape{},orig{};
 tape[0]=input;tape[8]=1;orig=tape;tape[1]=initial.w;
 int q=initial.z,h=initial.d;vector<int> rows;
 for(int tick=0;tick<160;tick++){
   if(q==(input?2:75)&&h==-2&&tape==orig)return {-1};
   if(h < -1 || h>7 ||q==50||q==254||q<0)return rows;
   int b=tape[h+1],row=q*2+b;
   if(!check)rows.push_back(row);
   A a=row==patch?alt:T[q][b];
   if(a.d==0)return rows;
   tape[h+1]=a.w;h+=a.d;q=a.z;
 }
 return rows;
}
bool pass(A a,int row,A b){for(int i=0;i<2;i++)if(trace(a,i,row,b,true)!=vector<int>{-1})return false;return true;}
int main(int argc,char**argv){
 ifstream f(argv[1]);string line;set<int> qs;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream s(line);s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};if(q!=50)qs.insert(q);}
 states.assign(qs.begin(),qs.end());
 for(int q:states)for(int w:{0,1})for(int d:{-1,1})acts.push_back({w,d,q});
 long tested=0,hits=0;
 for(A a:acts){
   T[34][0]=a;
   set<int> choices;
   for(int i=0;i<2;i++){auto tr=trace(a,i);for(int r:tr)if(r>=0&&r!=68&&r/2!=50)choices.insert(r);}
   for(int row:choices)for(A b:acts){if(b==T[row/2][row%2])continue;tested++;if(pass(a,row,b)){
      cout<<"{\"entry\":["<<a.w<<","<<a.d<<","<<a.z<<"],\"patch\":["<<row/2<<","<<row%2<<","<<b.w<<","<<b.d<<","<<b.z<<"]}"<<endl;hits++;
   }}
 }
 cerr<<"tested "<<tested<<" hits "<<hits<<"\n";
}
