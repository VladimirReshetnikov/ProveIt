// Search register permutations and one-row folds jointly, with on-demand
// partial-permutation assignments. Source-window screen, not a proof kernel.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <vector>
#include <map>
#include <string>
using namespace std;
struct Row {int w,d,n;};
struct Context {int q,bits,known;};
Row T[196][2];int regof[196],SK[9],phys[9],used;
vector<Context> C[196];vector<Context> cases;
int keepq,dropq;Row patch;long long nodes=0,candidates=0,found=0;
const int R=12,LIMIT=64;
int image(int q){return q==dropq?keepq:q;}
bool solve_case(int ci,int q,int pos,int word,int steps);
bool next_case(int ci){
 if(ci==(int)cases.size())return true;
 return solve_case(ci,keepq,0,cases[ci].bits,0);
}
bool solve_case(int ci,int q,int pos,int word,int steps){
 const auto &cc=cases[ci];
 int goal=(cc.bits&~(1<<R));int gq=SK[phys[regof[cc.q]]];
 for(;steps<LIMIT;steps++){
  ++nodes;
  if(steps>0&&q==gq&&pos==1&&word==goal)return next_case(ci+1);
  if(q>=196||pos < -R||pos>R||!(cc.known>>(pos+R)&1))return false;
  int b=word>>(pos+R)&1;Row a;
  if(q==keepq&&b==1)a=patch;
  else {
   a=T[q][b];
   if(b==1&&regof[q]>=0){
    int rg=regof[q];
    if(phys[rg]<0){
     int newword=(word&~(1<<(pos+R)))|(a.w<<(pos+R));
     for(int j=0;j<9;j++)if(!(used>>j&1)){
      phys[rg]=j;used|=1<<j;
      if(solve_case(ci,image(SK[j]),pos+a.d,newword,steps+1))return true;
      used^=1<<j;phys[rg]=-1;
     }
     return false;
    }
    a.n=SK[phys[rg]];
   }
  }
  word=(word&~(1<<(pos+R)))|(a.w<<(pos+R));pos+=a.d;q=image(a.n);
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;
 fill(regof,regof+196,-1);
 ifstream tf(argv[1]),cf(argv[2]),sf(argv[3]);ofstream out(argv[4]);
 int q,b,w,n;string d;
 while(tf>>q>>b>>w>>d>>n)T[q][b]={w,d=="R"?1:-1,n};
 int bits,known;
 while(cf>>q>>b>>bits>>known)if(b==1)C[q].push_back({q,bits,known});
 for(int j=0;j<9;j++)sf>>SK[j];
 int rg;vector<int>selectors;
 while(sf>>q>>rg){regof[q]=rg;selectors.push_back(q);}
 auto start=chrono::steady_clock::now();
 for(int ai=0;ai<(int)selectors.size();ai++)for(int bi=ai+1;bi<(int)selectors.size();bi++){
  keepq=selectors[ai];dropq=selectors[bi];
  auto a=T[keepq][0],bb=T[dropq][0];
  if(a.w!=bb.w||a.d!=bb.d||a.n!=bb.n)continue;
  cases.clear();
  // Interleave contexts at the two source controls, after trying both representatives.
  size_t maxn=max(C[keepq].size(),C[dropq].size());
  for(size_t i=0;i<maxn;i++){
   if(i<C[keepq].size())cases.push_back(C[keepq][i]);
   if(i<C[dropq].size())cases.push_back(C[dropq][i]);
  }
  for(int p=0;p<9;p++)for(int r=0;r<9;r++){
   if(p==r)continue;
   int ra=regof[keepq],rb=regof[dropq];
   if((ra==0&&p!=6)||(rb==0&&r!=6)||(ra!=0&&p==6)||(rb!=0&&r==6))continue;
   for(int dest=0;dest<=196;dest++)if(dest!=dropq)for(int write=0;write<2;write++)for(int dir:{-1,1}){
    fill(phys,phys+9,-1);phys[0]=6;used=1<<6;
    phys[ra]=p;phys[rb]=r;used|=(1<<p)|(1<<r);
    patch={write,dir,dest};++candidates;
    if(next_case(0)){
     ++found;
     out<<"FOUND "<<keepq<<' '<<dropq<<' '<<write<<' '<<dir<<' '<<dest<<" perm";
     for(int j:phys)out<<' '<<j;out<<'\n';out.flush();
     cerr<<"FOUND keep "<<keepq<<" drop "<<dropq<<" total "<<found<<'\n';
     // Keep partial maps: all completions remain eligible for the separate
     // all-natural source checker and literal startup search.
    }
   }
  }
  cerr<<"pair "<<keepq<<' '<<dropq<<" candidates "<<candidates<<" nodes "<<nodes<<" found "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
 }
 out<<"COUNTS "<<candidates<<' '<<nodes<<' '<<found<<'\n';
}
