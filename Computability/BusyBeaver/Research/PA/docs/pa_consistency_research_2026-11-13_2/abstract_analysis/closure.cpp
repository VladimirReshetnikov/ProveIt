#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
// All nine registers are tracked jointly in {0,...,K-2,>=K-1}.
// The top decrement has two successors; all other abstract operations are exact.
// This is a sound inductive overapproximation, not a trace sampler.
int main(int argc,char**argv){
  if(argc!=4){std::cerr<<"closure CFG RADIX OUTPUT\n";return 2;}
  int K=std::stoi(argv[2]),n; if(K<2||K>4)return 2;
  std::ifstream in(argv[1]);in>>n;if(!in||n!=3812)return 3;
  std::vector<std::array<int,4>> g(n);for(auto&r:g)for(auto&x:r)in>>x;if(!in)return 3;
  std::array<uint32_t,9>pow;pow[0]=1;for(int i=1;i<9;i++)pow[i]=pow[i-1]*K;
  const uint32_t masks=pow[8]*K;
  uint64_t count=uint64_t(masks)*n;
  std::vector<uint64_t> visited((count+63)/64);
  std::vector<uint32_t> queue;queue.reserve(2000000);
  auto seen=[&](uint32_t x){return (visited[x/64]>>(x%64))&1;};
  auto add=[&](uint32_t pc,uint32_t mask){uint32_t x=pc*masks+mask;if(!seen(x)){visited[x/64]|=uint64_t(1)<<(x%64);queue.push_back(x);}};
  add(25,std::min(K-1,2));
  for(size_t at=0;at<queue.size();at++){
    uint32_t id=queue[at],pc=id/masks,m=id%masks;
    auto [op,r,z,p]=g[pc];
    if(op==3)continue;
    if(op==2){add(z,m);continue;}
    unsigned val=(m/pow[r])%K;
    if(op==0){add(z,val==unsigned(K-1)?m:m+pow[r]);continue;}
    if(val==0)add(z,m);
    else {add(p,m-pow[r]);if(val==unsigned(K-1))add(p,m);}
  }
  std::vector<uint32_t> rows(n), values(n);
  uint64_t audited_edges=0;
  auto check=[&](uint32_t pc,uint32_t mask){audited_edges++;if(!seen(pc*masks+mask)){std::cerr<<"Not closed\n";std::exit(5);}};
  for(uint32_t id:queue){
    uint32_t pc=id/masks,m=id%masks; rows[pc]++;
    auto[op,r,z,p]=g[pc];if(op==3)continue;
    if(op==2){check(z,m);continue;}
    unsigned val=(m/pow[r])%K;values[pc]|=1u<<val;
    if(op==0)check(z,val==unsigned(K-1)?m:m+pow[r]);
    else if(val==0)check(z,m);
    else{check(p,m-pow[r]);if(val==unsigned(K-1))check(p,m);}
  }
  std::ofstream out(argv[3]);
  out<<"{\n\"radix\":"<<K<<",\"registers\":9,\"sites\":"<<n<<",\"seed_site\":25,\"seed\":[2,0,0,0,0,0,0,0,0],\"reachable_pairs\":"<<queue.size()<<",\"audited_edges\":"<<audited_edges<<",\"closure_verified\":true,\n\"unreachable_sites\":[";
  bool comma=false;for(int i=0;i<n;i++)if(!rows[i]){if(comma)out<<",";out<<i;comma=true;}
  out<<"],\n\"forced_zero\":[";comma=false;
  for(int i=0;i<n;i++)if(g[i][0]==1&&values[i]==1){if(comma)out<<",";out<<i;comma=true;}
  out<<"],\n\"forced_one\":[";comma=false;
  for(int i=0;i<n;i++)if(g[i][0]==1&&values[i]==2){if(comma)out<<",";out<<i;comma=true;}
  out<<"],\n\"site_data\":[";
  for(int i=0;i<n;i++){if(i)out<<",";out<<"["<<i<<","<<rows[i]<<","<<values[i]<<"]";}
  out<<"]\n}\n";std::cout<<"radix="<<K<<" pairs="<<queue.size()<<" audited_edges="<<audited_edges<<"\n";
}
