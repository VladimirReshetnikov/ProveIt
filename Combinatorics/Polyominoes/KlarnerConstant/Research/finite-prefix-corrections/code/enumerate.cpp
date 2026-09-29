// Independent Redelmeier-style fixed-polyomino enumerator.
// Translation classes are anchored at the leftmost cell on the bottom row.
// Updates occurrence counts incrementally; enumerate_direct.cpp scans every cell.
// Coordinates and pattern masks are independent of the Python reference encoding.
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>
using U64=std::uint64_t;
constexpr int W=65, ORIGIN=32+W*2, CAP=W*36;
std::array<bool,CAP> occupied{}, blocked{};
std::vector<int> cells;
std::array<unsigned,CAP> localmask{};
std::array<U64,17> current{};
int limit;
std::array<U64,33> totals{};
std::array<std::array<U64,17>,33> profile{};
const std::array<int,4> adjacent{1,-1,W,-W};
// Local mask bits: NW, NE, NEE, W, E, EE, SW, S, SE, SEE.
const std::array<int,10> offsets{-1+W,1+W,2+W,-1,1,2,-1-W,-W,1-W,2-W};
std::array<unsigned,1024> matches{};
unsigned mask(std::initializer_list<int> bits){unsigned m=0;for(int b:bits)m|=1u<<b;return m;}
void init_patterns(){
 const std::array<unsigned,17> req{0,0,0,0,0,0,1u<<4,1u<<4,1u<<4,1u<<4,1u<<4,1u<<4,(1u<<4)|(1u<<5),(1u<<4)|(1u<<5),1u<<4,1u<<4,1u<<4};
 const std::array<unsigned,17> ban{
 mask({0,1,3,4,6,7,8}),mask({0,3,4,6,7,8}),mask({3,4,6,7,8}),mask({6,7,8}),mask({3,6,7,8}),mask({0,3,6,7,8}),
 mask({7,8,9}),mask({3,6,7,8}),mask({0,3,6,7,8,9}),mask({0,3,6,7,8}),mask({3,6,7,8,9}),mask({6,7,8,9}),
 mask({3,6,7,8,9}),mask({0,3,6,7,8,9}),mask({3,5,6,7,8,9}),mask({0,3,5,6,7,8,9}),mask({0,2,3,5,6,7,8,9})};
 for(unsigned local=0;local<1024;++local)for(int i=0;i<17;++i)
  if((local&req[i])==req[i] && !(local&ban[i])) matches[local]|=1u<<i;
}
bool allowed(int p){int y=p/W-2,x=p%W-32;return y>0 || (y==0 && x>=0);}
void adjust(unsigned bits, bool add){
 while(bits){unsigned i=__builtin_ctz(bits); if(add)++current[i];else --current[i];bits&=bits-1;}
}
void insert_cell(int p){
 occupied[p]=true;
 unsigned local=0;
 for(unsigned j=0;j<offsets.size();++j)if(occupied[p+offsets[j]])local|=1u<<j;
 localmask[p]=local;adjust(matches[local],true);
 for(unsigned j=0;j<offsets.size();++j){int q=p-offsets[j];if(occupied[q]){
  unsigned old=matches[localmask[q]];localmask[q]|=1u<<j;unsigned now=matches[localmask[q]];
  adjust(old&~now,false);adjust(now&~old,true);
 }}
}
void erase_cell(int p){
 adjust(matches[localmask[p]],false);occupied[p]=false;localmask[p]=0;
 for(unsigned j=0;j<offsets.size();++j){int q=p-offsets[j];if(occupied[q]){
  unsigned old=matches[localmask[q]];localmask[q]&=~(1u<<j);unsigned now=matches[localmask[q]];
  adjust(old&~now,false);adjust(now&~old,true);
 }}
}
void record(){
 int n=cells.size();++totals[n];
 for(int i=0;i<17;++i)profile[n][i]+=current[i];
}
void visit(std::vector<int> frontier){
 std::vector<int> rejected;
 while(!frontier.empty()){
  int p=frontier.back();frontier.pop_back();
  insert_cell(p);cells.push_back(p);record();
  if((int)cells.size()<limit){
   std::vector<int> child=frontier;
   for(int off:adjacent){int q=p+off;
    if(!allowed(q)||occupied[q]||blocked[q])continue;
    bool found=false;for(int r:child)if(r==q){found=true;break;}
    if(!found)child.push_back(q);
   }
   visit(child);
  }
  cells.pop_back();erase_cell(p);blocked[p]=true;rejected.push_back(p);
 }
 for(int p:rejected)blocked[p]=false;
}
int main(int argc,char**argv){
 if(argc!=2){std::cerr<<"Usage: enumerate N\n";return 2;}
 try {
  std::size_t parsed=0; limit=std::stoi(argv[1],&parsed);
  if(argv[1][parsed] != '\0' || limit<1 || limit>18)
   throw std::invalid_argument("N must be 1..18");
 } catch(const std::exception& e) {
  std::cerr << "Invalid size: " << e.what() << "\n"; return 2;
 }
 init_patterns();visit({ORIGIN});
 std::cout<<"n,A,c,d,e,f,g,h,p,q,r,s,t,u,v,w,x,y,z\n";
 for(int n=1;n<=limit;++n){std::cout<<n<<","<<totals[n];for(U64 v:profile[n])std::cout<<","<<v;std::cout<<"\n";}
}
