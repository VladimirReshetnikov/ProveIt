#include <vector>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <cmath>
#include <chrono>
#include <string>

// Same recurrence as exact_counts.cpp with positive cumulative sums and
// normalized weights a_n/(n! mu^n), computed in native long double.
// Intended to diagnose scales, not to substitute for exact counts or proof.
struct Layer {
  int n;
  std::vector<std::vector<std::vector<long double>>> a;
  explicit Layer(int nn):n(nn),a(nn+1) {
    for(int s=n%2;s<=n;s+=2){
      int U=1+(n-s)/2;
      a[s].resize(U+1);
      for(int u=1;u<=U;++u) a[s][u].resize(s+u);
    }
  }
};
int main(int argc,char**argv){
  int N=argc>1?std::stoi(argv[1]):800;
  std::ofstream out(argc>2?argv[2]:"floating-counts.txt");
  const long double pi=acosl(-1),mu=8/(3*pi*pi);
  out<<std::setprecision(22)<<"0 1\n1 "<<1/mu<<"\n";
  Layer old(1); old.a[1][1][1]=1/mu;
  auto begin=std::chrono::steady_clock::now();
  for(int n=1;n<N;++n){
    Layer next(n+1);
    const long double scale=1/((n+1)*mu);
    for(int s=n%2;s<=n;s+=2){
      for(int u=1;u<(int)old.a[s].size();++u){
        auto &v=old.a[s][u]; int m=s+u;
        long double prefix=0,suffix=0;
        // Separate positive prefix and suffix sums avoid cancellation.
        for(int i=0;i<m;++i){
          prefix+=v[i]*scale;
          if(i<s) next.a[s-1][u+1][i]+=prefix;
          else next.a[s+1][u][i+1]+=prefix;
        }
        for(int i=m-1;i>=0;--i){
          if(i<s) next.a[s-1][u][i]+=suffix;
          else if(u>1 && i+1<s+u) next.a[s+1][u-1][i+1]+=suffix;
          suffix+=v[i]*scale;
        }
      }
    }
    // Kahan summation for the scalar total.
    long double answer=0,comp=0;
    for(auto const&s:next.a) for(auto const&u:s) for(auto v:u){
      long double y=v-comp,t=answer+y;comp=(t-answer)-y;answer=t;
    }
    out<<(n+1)<<' '<<answer<<'\n';out.flush();
    old=std::move(next);
    if((n+1)%25==0){
      double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();
      std::cerr<<"n="<<n+1<<" seconds="<<elapsed<<'\n';
    }
  }
}
