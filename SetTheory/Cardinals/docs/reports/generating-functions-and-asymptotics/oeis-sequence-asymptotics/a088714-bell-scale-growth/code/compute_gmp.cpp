#include <gmpxx.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <chrono>
#include <stdexcept>
int main(int argc,char** argv){
 try {
  int N=argc>1?std::stoi(argv[1]):1000;
  if(N<1 || N>10000) throw std::runtime_error("N must be between 1 and 10000");
  std::string path=argc>2?argv[2]:"coefficients.txt";
  std::vector<std::vector<mpz_class>> c(N+1);
  c[0].assign(N+2,mpz_class(1));
  std::ofstream out(path); if(!out)throw std::runtime_error("Cannot open output");
  out<<"0 1\n";
  auto start=std::chrono::steady_clock::now();
  for(int n=1;n<=N;++n){
   c[n].resize(N-n+2);
   for(int k=1;k<=N-n+1;++k){
    c[n][k]=c[n][k-1];
    for(int i=0;i<n;++i)
     mpz_addmul(c[n][k].get_mpz_t(),c[i][k].get_mpz_t(),c[n-1-i][k+1].get_mpz_t());
   }
   out<<n<<' '<<c[n][1]<<'\n';
   if(n%100==0){out.flush();std::cerr<<n<<" "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" seconds\n";}
  }
 } catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 1;}
}
