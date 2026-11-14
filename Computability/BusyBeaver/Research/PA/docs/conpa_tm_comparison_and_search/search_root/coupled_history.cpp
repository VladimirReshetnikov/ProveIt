// Enumerate both replacement rows together, permitting recursive use of them.
// Finite local certificates are a search screen; full symbolic validation follows.
#include <array>
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Act {int w,d,n;};
struct Case {int b,target; vector<int8_t> tape;};
int main(int argc,char**argv){
 if(argc<2)return 2;
 ifstream f(argv[1]);int n,qh,rad,limit,ncases;
 f>>n>>qh>>rad>>limit>>ncases;
 if(!f)return 3;
 if(argc>2)limit=stoi(argv[2]);
 vector<int> labels(n);for(auto&x:labels)f>>x;
 vector<array<Act,2>> rows(n);
 for(auto&rr:rows)for(auto&a:rr)f>>a.w>>a.d>>a.n;
 vector<Case> cases(ncases);
 for(auto&c:cases){f>>c.b>>c.target;c.tape.resize(2*rad+1);for(auto&x:c.tape){int y;f>>y;x=y;}}
 vector<Act> acts;
 for(int w=0;w<2;w++)for(int d:{-1,1})for(int q=0;q<n;q++)acts.push_back({w,d,q});
 auto check=[&](const Case&c,const Act&a0,const Act&a1){
  array<int8_t,512> tape;copy(c.tape.begin(),c.tape.end(),tape.begin());
  int h=rad,q=qh,diff=0;
  for(int step=0;step<limit;step++){
   if(h==rad+1&&q==c.target&&diff==0)return true;
   if(h<0||h>2*rad||tape[h]<0||q<0||q>=n)return false;
   const Act&a=q==qh?(tape[h]?a1:a0):rows[q][tape[h]];
   diff+=(a.w!=c.tape[h])-(tape[h]!=c.tape[h]);
   tape[h]=a.w;h+=a.d;q=a.n;
  }
  return false;
 };
 size_t tried=0,found=0,best=0;vector<size_t> hist(ncases+1);
 for(auto&a0:acts)for(auto&a1:acts){
  size_t k=0;
  while(k<cases.size()&&check(cases[k],a0,a1))k++;
  hist[k]++;tried++;
  if(k>best){best=k;cerr<<"best "<<best<<" / "<<cases.size()<<" tried "<<tried<<"\n";}
  if(k==cases.size()){
   found++;cout<<"SURVIVOR "<<a0.w<<" "<<a0.d<<" "<<labels[a0.n]<<" "<<a1.w<<" "<<a1.d<<" "<<labels[a1.n]<<"\n";cout.flush();
  }
 }
 cout<<"TRIED "<<tried<<" FOUND "<<found<<" BEST "<<best<<" CONTEXTS "<<ncases<<" LIMIT "<<limit<<"\n";
 cout<<"FAIL_COUNTS";for(size_t k=0;k<hist.size();k++)if(hist[k])cout<<" "<<k<<":"<<hist[k];cout<<"\n";
}
