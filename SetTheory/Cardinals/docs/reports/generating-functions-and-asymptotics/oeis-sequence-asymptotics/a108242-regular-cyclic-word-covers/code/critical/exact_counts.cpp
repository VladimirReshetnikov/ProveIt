// Exact cyclic-triple cover counts, independent of slot-partition asymptotics.
// Compile: g++ -O3 -std=c++17 exact_counts.cpp -lgmpxx -lgmp -o /tmp/cyclic-exact
// Run: /tmp/cyclic-exact n r
#include <gmpxx.h>
#include <unordered_map>
#include <vector>
#include <iostream>
#include <chrono>
#include <stdexcept>
using Integer=mpz_class;
struct Counts { Integer plus, minus; };
int R;
std::unordered_map<unsigned long long, Counts> memo;
unsigned long long key(const std::vector<int>& c) {
 unsigned long long z=0;
 for(int k=1;k<=R;k++) z|=(unsigned long long)c[k]<<(7*(k-1));
 return z;
}
Counts solve(std::vector<int>& c) {
 auto id=key(c); auto found=memo.find(id);
 if(found!=memo.end()) return found->second;
 int a=1; while(a<=R && c[a]==0) ++a;
 if(a>R) return Counts{1,1};
 Counts out{0,0}; --c[a];
 auto add=[&](int ar,int k,int kr,int l,int lr,int mult,int j){
  // k,l refer to residual classes before either other label is changed.
  if(k) --c[k]; if(l) --c[l];
  if(ar) ++c[ar]; if(kr) ++c[kr]; if(lr) ++c[lr];
  Counts sub=solve(c);
  out.plus+=mult*sub.plus;
  if(j%2) out.minus+=mult*sub.minus; else out.minus-=mult*sub.minus;
  if(ar) --c[ar]; if(kr) --c[kr]; if(lr) --c[lr];
  if(k) ++c[k]; if(l) ++c[l];
 };
 for(int j=1;j<=a;j++) {
  if(3*j<=a) add(a-3*j,0,0,0,0,3,j); // iii
  if(2*j<=a) for(int k=j;k<=R;k++) if(c[k])
   add(a-2*j,k,k-j,0,0,2*c[k],j); // iik
  for(int k=2*j;k<=R;k++) if(c[k])
   add(a-j,k,k-2*j,0,0,c[k],j); // ikk
  for(int k=j;k<=R;k++) if(c[k]) for(int l=k;l<=R;l++) {
   int ways=(k==l)?c[k]*(c[k]-1)/2:c[k]*c[l];
   if(ways) add(a-j,k,k-j,l,l-j,2*ways,j); // two orientations of ikl
  }
 }
 ++c[a];
 if(out.plus%a!=0 || out.minus%a!=0) throw std::runtime_error("nonintegral recurrence");
 out.plus/=a;out.minus/=a;
 if(out.plus<0||out.minus<0) throw std::runtime_error("negative count");
 memo.emplace(id,out);return out;
}
int main(int argc,char**argv) {
 if(argc!=3){std::cerr<<"usage: exact_counts n r\n";return 2;}
 int n=std::stoi(argv[1]);R=std::stoi(argv[2]);
 if(n<0||n>127||R<1||R>9){std::cerr<<"requires 0<=n<=127 and 1<=r<=9\n";return 2;}
 if(n*R%3){std::cout<<"{\"n\":"<<n<<",\"r\":"<<R<<",\"plus\":\"0\",\"minus\":\"0\",\"states\":0}\n";return 0;}
 std::vector<int> c(R+1);c[R]=n;
 auto start=std::chrono::steady_clock::now();auto v=solve(c);
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::cout<<"{\"n\":"<<n<<",\"r\":"<<R<<",\"plus\":\""<<v.plus<<"\",\"minus\":\""<<v.minus<<"\",\"states\":"<<memo.size()<<",\"seconds\":"<<sec<<"}\n";
}
