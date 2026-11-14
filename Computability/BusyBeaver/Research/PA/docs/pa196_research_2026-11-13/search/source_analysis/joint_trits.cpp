#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
// Saturating product abstraction: each register lies in {0}, {1}, or {2,...}.
// Each exact successor has an abstract successor listed by this program.
int main(int argc, char** argv) {
  if(argc != 3 && argc != 4) throw std::runtime_error("graph.txt output-bitset.bin [categories] required");
  const int categories=argc==4?std::stoi(argv[3]):3;
  if(categories<2 || categories>4)throw std::runtime_error("supported category count 2..4");
  std::ifstream in(argv[1]);
  int n; in >> n;
  if(n != 3812) throw std::runtime_error("unexpected source count");
  std::vector<std::array<int,4>> graph(n);
  for(auto& r:graph) {
    in >> r[0];
    if(r[0]==1) in >> r[1];
    if(r[0]==2) in >> r[1] >> r[2];
    if(r[0]==3) in >> r[1] >> r[2] >> r[3];
    if(!in) throw std::runtime_error("bad graph");
  }
  std::array<int,9> p{}; p[0]=1; for(int j=1;j<9;++j)p[j]=p[j-1]*categories;
  const int codes = p[8]*categories;
  std::vector<uint64_t> seen((uint64_t(n)*codes+63)/64,0);
  std::vector<uint32_t> todo;
  auto add=[&](int pc,int code){
    if(pc<0 || pc>=n || code<0 || code>=codes)throw std::runtime_error("bad successor");
    uint32_t key=pc*codes+code;uint64_t mask=uint64_t(1)<<(key%64);
    if(!(seen[key/64]&mask)){seen[key/64]|=mask;todo.push_back(key);}
  };
  const int seed=std::min(2,categories-1);
  add(25,seed); // exact seed (2,0,0,0,0,0,0,0,0).
  for(size_t k=0;k<todo.size();++k){
    int pc=todo[k]/codes,c=todo[k]%codes;auto r=graph[pc];
    if(r[0]==0)continue;
    if(r[0]==1){add(r[1],c);continue;}
    int d=c/p[r[1]]%categories;
    if(r[0]==2){add(r[2],c+(d<categories-1?p[r[1]]:0));continue;}
    if(d==0){add(r[2],c);continue;}
    add(r[3],c-p[r[1]]);
    if(d==categories-1)add(r[3],c);
  }
  std::vector<std::array<int,9>> inventory(n);
  std::vector<int> site_counts(n,0);
  for(uint32_t key:todo){
    int pc=key/codes,c=key%codes; ++site_counts[pc];
    for(int j=0;j<9;++j)inventory[pc][j]|=1<<(c/p[j]%categories);
  }
  // Separate closure audit over the persisted fixed point, not the worklist.
  uint64_t audited=0, edges=0;
  auto has=[&](int pc,int code){uint32_t key=pc*codes+code;return bool(seen[key/64]&(uint64_t(1)<<(key%64)));};
  auto check=[&](int pc,int c){++edges;if(!has(pc,c))throw std::runtime_error("not closed");};
  if(!has(25,seed))throw std::runtime_error("seed missing");
  for(int pc=0;pc<n;++pc)for(int c=0;c<codes;++c)if(has(pc,c)){
    ++audited;auto r=graph[pc];
    if(r[0]==0)continue;
    if(r[0]==1){check(r[1],c);continue;}
    int d=c/p[r[1]]%categories;
    if(r[0]==2){check(r[2],c+(d<categories-1?p[r[1]]:0));continue;}
    if(d==0){check(r[2],c);continue;}
    check(r[3],c-p[r[1]]);
    if(d==categories-1)check(r[3],c);
  }
  if(audited!=todo.size())throw std::runtime_error("audit count differs");
  std::ofstream out(argv[2],std::ios::binary);
  for(auto word:seen)for(int byte=0;byte<8;++byte)out.put((word>>(8*byte))&255);
  std::cout<<"{\"categories\":"<<categories<<",\"reachable_pairs\":"<<todo.size()<<",\"closure_edges\":"<<edges<<",\"unreachable_sites\":[";
  bool first=true;
  for(int pc=0;pc<n;++pc)if(!site_counts[pc]){if(!first)std::cout<<",";first=false;std::cout<<pc;}
  std::cout<<"],\"forced_zero\":["; first=true;
  for(int pc=0;pc<n;++pc)if(graph[pc][0]==3 && inventory[pc][graph[pc][1]]==1){if(!first)std::cout<<",";first=false;std::cout<<pc;}
  std::cout<<"],\"forced_positive\":[";first=true;
  for(int pc=0;pc<n;++pc)if(graph[pc][0]==3 && inventory[pc][graph[pc][1]] && !(inventory[pc][graph[pc][1]]&1)){if(!first)std::cout<<",";first=false;std::cout<<pc;}
  std::cout<<"],\"closure_audited\":true,\"abstract_halt_reachable\":";
  bool h=false;for(int pc=0;pc<n;++pc)if(graph[pc][0]==0 && site_counts[pc])h=true;
  std::cout<<(h?"true":"false")<<"}\n";
}
