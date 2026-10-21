#define main fold_program_main
#include "fold2.cpp"
#undef main
#include <cassert>
#include <fstream>
#include <sstream>
int main(int argc,char **argv){
 assert(argc==2);std::ifstream f(argv[1]);std::string l;
 for(auto &r:T)for(auto&a:r)a={0,0,-2};
 while(std::getline(f,l)){if(l.empty()||l[0]=='#')continue;int q,b,w,z;char d;std::istringstream s(l);s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};}
 T[69][0]={0,1,105};T[400][0]={0,1,104};T[400][1]={1,1,31};T[100][0]={0,1,400};
 Ctx one{bit(-1),bit(-1)},zero{bit(-1),0};
 assert(block(69,69,400,0,{0,-1,213},one,false));
 assert(block(400,69,400,0,{0,-1,213},zero,false));
 assert(!block(69,69,400,0,{0,1,254},one,false));
 assert(!block(8,8,127,1,{1,-1,110},one,false));
 assert(!block(127,8,127,1,{1,-1,110},zero,false));
 // A genuine two-row marker fold: both old rows differ and both local
 // replacement proofs close without touching the other changed row.
 for(auto &r:T)for(auto&a:r)a={0,0,-2};
 T[1][0]={0,1,7};T[1][1]={1,1,8};
 T[2][0]={0,1,9};T[2][1]={1,1,10};
 T[3][0]={0,1,6};T[3][1]={1,1,5};
 T[5][0]={0,1,7};T[5][1]={1,1,8};
 T[6][0]={0,1,9};T[6][1]={1,1,10};
 for(int b=0;b<2;++b){
  assert(block(1,1,2,b,{b,-1,3},one,true));
  assert(block(2,1,2,b,{b,-1,3},zero,true));
  assert(!block(1,1,2,b,{b,-1,3},zero,true));
  assert(!block(1,1,2,b,{b,-1,3},Ctx{},true));
 }
 std::cout<<"PASS known 69/400 fold, early-halt rejection, cyclic-provider rejection, two-row marker fold, wrong and unknown marker rejection"<<std::endl;
}
