#include <gmpxx.h>
#include <vector>
#include <fstream>
#include <iostream>
#include <string>
#include <chrono>

// Exact forward compacted-state recurrence for OEIS A202058.
// State after n letters: s once-used labels, u unused available labels,
// and last-value rank k, with n-s even, 0<=s<=n, 1<=u<=1+(n-s)/2.
// Four transitions are those of the frozen report's equation (children).
// Prefix/suffix sums over old k reduce the running time to O(N^4)
// big-integer additions and storage to O(N^3) big integers.
struct Layer {
  int n;
  std::vector<std::vector<std::vector<mpz_class>>> a;
  explicit Layer(int nn):n(nn),a(nn+1) {
    for(int s=n%2;s<=n;s+=2){
      int U=1+(n-s)/2;
      a[s].resize(U+1);
      for(int u=1;u<=U;++u) a[s][u].resize(s+u);
    }
  }
};

int main(int argc,char**argv){
  int N=argc>1?std::stoi(argv[1]):200;
  std::ofstream out(argc>2?argv[2]:"exact-counts.txt");
  out<<"0 1\n1 1\n";
  Layer old(1); old.a[1][1][1]=1;
  auto begin=std::chrono::steady_clock::now();
  for(int n=1;n<N;++n){
    Layer next(n+1);
    for(int s=n%2;s<=n;s+=2){
      for(int u=1;u<(int)old.a[s].size();++u){
        auto &v=old.a[s][u];
        int m=s+u;
        mpz_class total=0,prefix=0;
        for(auto const&x:v) total+=x;
        if(total==0) continue;
        // At index i prefix=sum_{k<=i} P_n(s,u,k).
        for(int i=0;i<m;++i){
          prefix+=v[i];
          if(i<s){
            next.a[s-1][u+1][i]+=prefix; // duplicate ascent
            // i==m-1 cannot occur here since u>=1.
            next.a[s-1][u][i]+=total-prefix; // duplicate non-ascent
          } else {
            next.a[s+1][u][i+1]+=prefix; // new ascent
            if(u>1 && i+1<s+u)
              next.a[s+1][u-1][i+1]+=total-prefix; // new non-ascent
          }
        }
      }
    }
    mpz_class answer=0;
    for(auto const&s:next.a) for(auto const&u:s) for(auto const&v:u) answer+=v;
    out<<(n+1)<<' '<<answer<<'\n'; out.flush();
    old=std::move(next);
    if((n+1)%10==0){
      double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();
      std::cerr<<"n="<<n+1<<" seconds="<<elapsed<<" digits="<<answer.get_str().size()<<'\n';
    }
  }
}
