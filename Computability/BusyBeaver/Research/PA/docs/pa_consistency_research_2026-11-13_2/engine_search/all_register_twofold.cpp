// Joint two-row contextual fold and register-order synthesis.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Row{int w,d,n;};struct Ctx{int q,b,bits,known;};
Row T[196][2],patch[2];int rof[196],SK[9],phy[9],used,dropq,keepq;
vector<Ctx>C[196][2],cases,allcases,zerocases,reps;
bool unknown1=false;long long calls=0,found=0;
const int R=12, LIMIT=64;
int image(int q){return q==dropq?keepq:q;}
bool solve_case(int ci,int q,int pos,int word,int steps);
bool next_case(int ci){
 if(ci==(int)cases.size())return true;
 const auto&cc=cases[ci];
 if(cc.b==1&&rof[cc.q]>=0&&phy[rof[cc.q]]<0){
  int r=rof[cc.q];
  for(int j=0;j<9;j++)if(!(used>>j&1)){
   phy[r]=j;used|=1<<j;
   if(solve_case(ci,keepq,0,cc.bits,0))return true;
   phy[r]=-1;used^=1<<j;
  }
  return false;
 }
 return solve_case(ci,keepq,0,cc.bits,0);
}
bool solve_case(int ci,int q,int pos,int word,int steps){
 const auto &cc=cases[ci];Row orig=T[cc.q][cc.b];
 if(cc.b==1&&rof[cc.q]>=0)orig.n=SK[phy[rof[cc.q]]];
 int goal=(cc.bits&~(1<<R))|orig.w<<R,gq=image(orig.n),gp=orig.d;
 for(;steps<LIMIT;steps++){
  ++calls;
  if(steps&&q==gq&&pos==gp&&word==goal)return next_case(ci+1);
  if(q>=196||pos < -R||pos>R||!(cc.known>>(pos+R)&1))return false;
  int b=word>>(pos+R)&1;Row a;
  if(q==keepq){
   if(b==1&&unknown1)return next_case(ci+1);
   a=patch[b];
  }else{
   a=T[q][b];
   if(b==1&&rof[q]>=0){
    int r=rof[q];
    if(phy[r]<0){
     int nw=(word&~(1<<(pos+R)))|a.w<<(pos+R);
     for(int j=0;j<9;j++)if(!(used>>j&1)){
      phy[r]=j;used|=1<<j;
      if(solve_case(ci,image(SK[j]),pos+a.d,nw,steps+1))return true;
      phy[r]=-1;used^=1<<j;
     }
     return false;
    }
    a.n=SK[phy[r]];
   }
  }
  word=(word&~(1<<(pos+R)))|a.w<<(pos+R);pos+=a.d;q=image(a.n);
 }
 return false;
}
void resetperm(){fill(phy,phy+9,-1);used=0;}
int main(int argc,char**argv){
 if(argc!=5)return 2;
 fill(rof,rof+196,-1);ifstream tf(argv[1]),cf(argv[2]),sf(argv[3]);ofstream out(argv[4]);
 int q,b,w,n,bits,known;string d;
 while(tf>>q>>b>>w>>d>>n)T[q][b]={w,d=="R"?1:-1,n};
 while(cf>>q>>b>>bits>>known)C[q][b].push_back({q,b,bits,known});
 for(int j=0;j<9;j++){sf>>SK[j];}
 int rg;
 while(sf>>q>>rg)rof[q]=rg;
 long long pairs=0,p0count=0,viable=0,p1count=0,firstpass=0;
 auto start=chrono::steady_clock::now();
 for(keepq=0;keepq<196;keepq++)for(dropq=keepq+1;dropq<196;dropq++){
  // All control pairs admitted, including pairs using selector rows only as helpers.
  if(C[keepq][0].empty()||C[keepq][1].empty()||C[dropq][0].empty()||C[dropq][1].empty())continue;
  ++pairs;allcases.clear();zerocases.clear();reps.clear();
  for(int b:{1,0}){
   for(int qq:{keepq,dropq})reps.push_back(C[qq][b][0]);
   size_t maxn=max(C[keepq][b].size(),C[dropq][b].size());
   for(size_t i=0;i<maxn;i++)for(int qq:{keepq,dropq})if(i<C[qq][b].size()){
    allcases.push_back(C[qq][b][i]);if(b==0)zerocases.push_back(C[qq][b][i]);
   }
  }
  for(int n0=0;n0<=196;n0++)if(n0!=dropq)for(int w0=0;w0<2;w0++)for(int d0:{-1,1}){
   ++p0count;patch[0]={w0,d0,n0};unknown1=true;cases=zerocases;resetperm();
   if(!next_case(0))continue;
   ++viable;unknown1=false;
   for(int n1=0;n1<=196;n1++)if(n1!=dropq)for(int w1=0;w1<2;w1++)for(int d1:{-1,1}){
    ++p1count;patch[1]={w1,d1,n1};cases=reps;resetperm();
    if(!next_case(0))continue;
    ++firstpass;cases=allcases;resetperm();
    if(!next_case(0))continue;
    ++found;out<<"FOUND "<<keepq<<' '<<dropq<<' '<<w0<<' '<<d0<<' '<<n0<<' '<<w1<<' '<<d1<<' '<<n1<<" perm";
    for(int j:phy)out<<' '<<j;
    out<<'\n';out.flush();cerr<<"FOUND "<<found<<" pair "<<keepq<<' '<<dropq<<'\n';
   }
  }
  if(pairs%50==0)cerr<<"pairs "<<pairs<<" p0 "<<p0count<<" viable "<<viable<<" p1 "<<p1count<<" firstpass "<<firstpass<<" found "<<found<<" calls "<<calls<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
 }
 cerr<<"DONE pairs "<<pairs<<" p0 "<<p0count<<" viable "<<viable<<" p1 "<<p1count<<" firstpass "<<firstpass<<" found "<<found<<" calls "<<calls<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
}
