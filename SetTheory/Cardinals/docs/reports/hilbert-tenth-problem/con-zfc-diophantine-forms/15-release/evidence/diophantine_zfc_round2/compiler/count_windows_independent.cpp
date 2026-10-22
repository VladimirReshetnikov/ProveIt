// Newly authored independent enumeration. No imported repository scripts.
// Enumerates all 439 centers and all left/right pairs, with exact
// predecessor/successor multiplicity and independent corner weights.
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using I=__int128_t;
constexpr int A=439, L=434,Q=435,R=436,V=437,H=438;
struct Cell { int bit,state; bool vertical,horizontal,phase; };
struct Action {int bit,move,state;};
std::array<Cell,A> cells;
Action tm[216][2];
std::string decimal(I n) { if(!n)return "0"; std::string s; while(n){s.insert(s.begin(),'0'+n%10); n/=10;}return s; }
bool head(int c){return cells[c].state>=0;}
int corners(int c){return head(c)?36:5232;}
bool phase_pair(int l,int r){return (l==L&&(r==L||r==Q))||(l==Q&&r==R)||(l==R&&r==R);}
// Check precisely the five-cell center predicate. p is previous time; n is next time.
bool allowed(int l,int c,int r,int p,int n){
 auto a=cells[c],ll=cells[l],rr=cells[r],pp=cells[p],nn=cells[n];
 if(a.vertical!=nn.vertical || (a.vertical&&rr.vertical) || (a.horizontal&&nn.horizontal))return false;
 if(!a.vertical&&!rr.vertical&&a.horizontal!=rr.horizontal)return false;
 if(a.vertical||a.horizontal)return true;
 if(a.phase!=pp.horizontal)return false;
 if(a.phase){
   if(ll.vertical&&c!=L)return false;
   if(rr.vertical&&c!=R)return false;
   if(!rr.vertical&&!phase_pair(c,r))return false;
 }
 if(nn.horizontal&&a.state>=0&&a.state!=215)return false;
 if(a.state>=0){int m=tm[a.state][a.bit].move;if((m<0&&ll.vertical)||(m>0&&rr.vertical))return false;}
 if(nn.horizontal)return true;
 if(ll.horizontal||rr.horizontal)return false;
 int outbit=a.state<0?a.bit:tm[a.state][a.bit].bit, outstate=-1, arrivals=0;
 for(auto [old,needed]:{std::pair{ll,1},std::pair{a,0},std::pair{rr,-1}}){
  if(old.state>=0&&tm[old.state][old.bit].move==needed){outstate=tm[old.state][old.bit].state;++arrivals;}
 }
 return arrivals<=1&&nn.bit==outbit&&nn.state==outstate;
}
int main(int argc,char**argv){
 assert(argc==2);std::ifstream in(argv[1]);std::string line;int rows=0;
 while(std::getline(in,line)){if(line.empty()||line[0]=='#')continue;std::istringstream s(line);int q,b,w,t;char m;s>>q>>b>>w>>m>>t;tm[q][b]={w,m=='R'?1:-1,t};++rows;}
 assert(rows==430);tm[215][0]={0,0,215};tm[215][1]={1,0,215};
 for(int c=0;c<434;++c)cells[c]={c%2,c/2-1,false,false,false};
 cells[L]={0,-1,false,false,true};cells[Q]={0,0,false,false,true};cells[R]={0,-1,false,false,true};
 cells[V]={-1,-1,true,false,false};cells[H]={-1,-1,false,true,false};
 assert(allowed(L,Q,R,H,1));assert(allowed(0,V,H,H,V));
 I crosses=0,pruned=0;std::cout<<"{\n\"centers\": [\n";
 for(int c=0;c<A;++c){
  I local=0,small=0;int p=c>=V?0:cells[c].phase?H:0;
  int pm=c>=V?439:cells[c].phase?1:438;
  int pw=c>=V?46980:cells[c].phase?5232:41748;
  for(int l=0;l<A;++l)for(int r=0;r<A;++r){
   std::vector<int> ns;
   if(c==V)ns.push_back(V);
   else if(c==H){ // All 437 possible following interior symbols have the same center truth value.
    if(allowed(l,c,r,p,0)){local+=I(pm)*437;if(head(l)+head(c)+head(r)<=1)small+=I(pw)*(433*36+4*5232);}
    continue;
   } else {
    ns.push_back(H);
    if(l!=H&&r!=H){
     auto cc=cells[c];int outbit=cc.state<0?cc.bit:tm[cc.state][cc.bit].bit, outstate=-1, n=0;
     for(auto [s,m]:{std::pair{l,1},std::pair{c,0},std::pair{r,-1}}){auto old=cells[s];if(old.state>=0&&tm[old.state][old.bit].move==m){outstate=tm[old.state][old.bit].state;++n;}}
     if(n<=1){ns.push_back(2*(outstate+1)+outbit);if(outbit==0&&outstate==-1){ns.push_back(L);ns.push_back(R);}if(outbit==0&&outstate==0)ns.push_back(Q);}
    }
   }
   for(int n:ns)if(allowed(l,c,r,p,n)){
     local+=pm;
     if(head(l)+head(c)+head(r)<=1)small+=I(pw)*corners(n);
   }
  }
  crosses+=local;pruned+=small;
  std::cout<<"{\"code\":"<<c<<",\"crosses\":"<<decimal(local)<<",\"row_head_limited_windows\":"<<decimal(small)<<"}"<<(c==A-1?"\n":",\n");
 }
 std::cout<<"],\n\"crosses\":"<<decimal(crosses)<<",\n\"windows\":"<<decimal(crosses*I(A)*A*A*A)<<",\n\"row_head_limited_windows\":"<<decimal(pruned)<<"\n}\n";
}
