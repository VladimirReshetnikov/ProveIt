#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <climits>
#include <vector>
#include <fstream>
#include <iostream>
struct Tr{int w,d,q;};
int main(int argc,char**argv){
 if(argc<2)return 2;
 Tr t[300][2];for(auto& r:t)for(auto& z:r)z={0,0,300};
 std::ifstream in(argv[1]);int q,b,w,n;char d;int num=0;
 while(in>>q>>b>>w>>d>>n){t[q][b]={w,d=='R'?1:-1,n};num=std::max(num,q+1);}
 long long limit=argc>2?atoll(argv[2]):3000000;
 const int N=1<<23,C=N/2;std::vector<unsigned char>a(N);
 int successes=0;
 for(int start=0;start<num;start++){
  std::fill(a.begin(),a.end(),0);q=start;int h=C,lo=INT_MAX,hi=-1,ones=0;bool found=false;
  long long k;
  for(k=0;k<limit && q<num && h>2 && h<N-3;k++){
   if(q==75 && a[h-1] && lo==h-1 && a[h]){
    int j=h+1;while(j<=hi && !a[j])++j;
    int header=j,dist=j-h;
    if(dist>=48 && j<=hi){
     ++j;std::vector<int>vs;bool valid=true;
     while(j<=hi){
      if(a[j]){valid=false;break;}++j;int len=0;
      while(j<=hi && a[j]){++len;++j;}
      if(len==0){valid=false;break;}vs.push_back(len-1);
     }
     if(valid && vs.size()>=10){
      for(int z=0;z<9;z++)if(z!=6 && vs[z]!=0)valid=false;
      if(valid){
       std::cout<<"MATCH start="<<start<<" steps="<<k<<" head="<<h-C<<" candidate="<<vs[6]<<" gap="<<dist<<" registers=";
       for(int v:vs)std::cout<<v<<",";std::cout<<"\n"<<std::flush;
       found=true;++successes;break;
      }
     }
    }
   }
   auto tr=t[q][a[h]];if(tr.w!=a[h]){
    if(tr.w){++ones;lo=std::min(lo,h);hi=std::max(hi,h);}
    else{--ones;if(!ones){lo=INT_MAX;hi=-1;}else{if(h==lo){++lo;while(!a[lo])++lo;}if(h==hi){--hi;while(!a[hi])--hi;}}}
    a[h]=tr.w;
   }
   h+=tr.d;q=tr.q;
  }
  if(!found && (start%16==0 || q>=num))std::cout<<"END start="<<start<<" steps="<<k<<" state="<<q<<" ones="<<ones<<" head="<<h-C<<"\n"<<std::flush;
 }
 std::cout<<"DONE matches="<<successes<<"\n";
}
