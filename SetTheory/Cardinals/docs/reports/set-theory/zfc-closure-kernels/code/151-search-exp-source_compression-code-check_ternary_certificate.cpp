// Independent local-closure audit: no worklist or reachability recomputation.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
#include <stdexcept>
using namespace std;
void require(bool b,const char*s){if(!b)throw runtime_error(s);}
int main(int argc,char**argv){
 require(argc==3,"usage graph bitmap");ifstream gf(argv[1]);int n;gf>>n;require(n==4744,"ordinal count");vector<array<int,4>> g(n);for(auto&r:g)for(int&x:r)gf>>x;require(bool(gf),"graph read");
 const int C=19683;const array<int,9> p={1,3,9,27,81,243,729,2187,6561};
 ifstream bf(argv[2],ios::binary|ios::ate);require(bool(bf),"bitmap exists");require(bf.tellg()==int64_t(n)*C,"bitmap byte count");bf.seekg(0);vector<uint8_t>a(size_t(n)*C);bf.read(reinterpret_cast<char*>(a.data()),a.size());require(bool(bf),"bitmap complete");
 require(a[2*p[0]+2*p[4]]==1,"seed class 3,0,0,0,3,0,0,0,0");
 uint64_t configurations=0,edges=0;array<unsigned,9> at4564{};
 auto included=[&](int j,int m){require(0<=j&&j<n&&0<=m&&m<C,"successor range");require(a[size_t(j)*C+m]==1,"local closure missing");++edges;};
 for(int i=0;i<n;++i){auto [op,r,z,pos]=g[i];require(0<=op&&op<=3,"opcode");if(op<=1)require(0<=r&&r<9,"register");
  for(int m=0;m<C;++m){auto v=a[size_t(i)*C+m];require(v<=1,"bitmap Boolean");if(!v)continue;++configurations;
   if(i==4564)for(int k=0;k<9;++k)at4564[k]|=1U<<((m/p[k])%3);
   if(op==3)continue;
   if(op==2){included(z,m);continue;}
   const int digit=(m/p[r])%3,base=m-digit*p[r];
   if(op==0){static const int inc[3]={1,2,2};included(z,base+inc[digit]*p[r]);}
   else if(digit==0)included(z,m);
   else {included(pos,base+(digit-1)*p[r]);if(digit==2)included(pos,base+2*p[r]);}
  }
 }
 require(at4564[0]==4 && at4564[1]==4,"r0/r1 lower bounds at4564");
 require(a[size_t(4564)*C+1+3]==0,"reported counterexample excluded");
 cout<<"{\"status\":\"PASS\",\"configurations\":"<<configurations<<",\"closure_edges\":"<<edges<<",\"seed_class_code\":164,\"ordinal4564_register_class_masks\":[";
 for(int k=0;k<9;++k){if(k)cout<<',';cout<<at4564[k];}cout<<"],\"ordinal4564_r0_and_r1_at_least_two\":true}"<<endl;
}
