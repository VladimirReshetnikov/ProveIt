// Repair each shared branch by changing one existing helper row.
// Each emitted candidate still requires global source-contract validation.
#include <array>
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Act {int w,d,n;};
struct Case {int b,target;vector<int8_t> tape;};
int main(int argc,char**argv){
 if(argc<2)return 2;
 ifstream f(argv[1]);int n,qh,rad,limit,ncases;f>>n>>qh>>rad>>limit>>ncases;
 if(!f)return 3;
 if(argc>2)limit=stoi(argv[2]);
 vector<int> labels(n);for(auto&x:labels)f>>x;
 vector<array<Act,2>>rows(n);for(auto&rr:rows)for(auto&a:rr)f>>a.w>>a.d>>a.n;
 vector<Case>cases(ncases);for(auto&c:cases){f>>c.b>>c.target;c.tape.resize(2*rad+1);for(auto&x:c.tape){int y;f>>y;x=y;}}
 vector<Act>acts;for(int w=0;w<2;w++)for(int d:{-1,1})for(int q=0;q<n;q++)acts.push_back({w,d,q});
 auto check=[&](const Case&c,int rq,int rb,const Act&replacement){
  array<int8_t,512>tape;copy(c.tape.begin(),c.tape.end(),tape.begin());int h=rad,q=qh,diff=0;
  for(int step=0;step<limit;step++){
   if(h==rad+1&&q==c.target&&diff==0)return true;
   if(h<0||h>2*rad||tape[h]<0||q<0||q>=n)return false;
   const Act&a=(q==rq&&tape[h]==rb)?replacement:rows[q][tape[h]];
   diff+=(a.w!=c.tape[h])-(tape[h]!=c.tape[h]);tape[h]=a.w;h+=a.d;q=a.n;
  }return false;
 };
 for(int bit=0;bit<2;bit++){
  vector<Case>cx;for(auto&c:cases)if(c.b==bit)cx.push_back(c);
  size_t tried=0,found=0,best=0;
  for(int q=0;q<n;q++)for(int b=0;b<2;b++)for(auto&a:acts){
   if(q==qh)continue;
   size_t k=0;while(k<cx.size()&&check(cx[k],q,b,a))k++;
   tried++;best=max(best,k);
   if(k==cx.size()){
    found++;cout<<"SURVIVOR "<<bit<<" "<<labels[q]<<" "<<b<<" "<<a.w<<" "<<a.d<<" "<<labels[a.n]<<"\n";cout.flush();
   }
  }
  cout<<"TRIED "<<bit<<" "<<tried<<" FOUND "<<found<<" BEST "<<best<<" CONTEXTS "<<cx.size()<<" LIMIT "<<limit<<"\n";
 }
}
