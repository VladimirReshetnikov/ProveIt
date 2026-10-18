#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

// Exact reachability in a finite joint abstraction. Atom0={0}, atom1={1},
// atom2={2,3,...}. All nine atoms are kept jointly rather than componentwise.
// Input masks are independently certified allowed site/register atoms.
int main(int argc,char**argv){
  if(argc!=3){std::cerr<<"usage: partition_cfg input output\n";return 2;}
  std::ifstream in(argv[1]);
  int n,start,root;in>>n>>start>>root;
  if(!in||n!=6460)return 3;
  struct Site {int op,r,pos,zero;std::array<int,9> allowed;};
  std::vector<Site> sites(n);
  for(auto& s:sites){in>>s.op>>s.r>>s.pos>>s.zero;for(auto& a:s.allowed)in>>a;}
  if(!in)return 4;
  constexpr int range=19683;std::array<int,9> power;
  power[0]=1;for(int r=1;r<9;r++)power[r]=3*power[r-1];
  std::array<std::array<uint8_t,9>,range> digits{};
  for(int a=0;a<range;a++){int t=a;for(int r=0;r<9;r++){digits[a][r]=t%3;t/=3;}}
  std::vector<uint64_t> visited((n*uint64_t(range)+63)/64,0);
  std::vector<uint32_t> queue;queue.reserve(1000000);
  auto add=[&](int s,int a){
    if(s<0)return;
    for(int r=0;r<9;r++)if(!(sites[s].allowed[r]&(1<<digits[a][r])))return;
    uint32_t key=s*range+a;uint64_t mask=uint64_t(1)<<(key%64);
    if(!(visited[key/64]&mask)){visited[key/64]|=mask;queue.push_back(key);}
  };
  add(start,root);
  std::vector<uint8_t> guards(n,0);
  for(size_t at=0;at<queue.size();at++){
    const uint32_t key=queue[at];int site=key/range,atoms=key%range;
    const auto& s=sites[site];
    if(s.op==1){int a=digits[atoms][s.r];add(s.pos,atoms+(a==2?0:power[s.r]));}
    else if(s.op==2){int a=digits[atoms][s.r];
      if(a==0){guards[site]|=1;add(s.zero,atoms);}
      else if(a==1){guards[site]|=2;add(s.pos,atoms-power[s.r]);}
      else{guards[site]|=2;add(s.pos,atoms-power[s.r]);add(s.pos,atoms);}
    }
    else if(s.op!=3)add(s.pos,atoms);
  }
  std::ofstream out(argv[2]);
  out<<"{\"status\":\"PASS\",\"joint_abstract_states\":"<<queue.size()<<",\"dead_leaves\":[";
  std::vector<int> counts(n,0);for(auto key:queue)counts[key/range]++;
  bool comma=false;
  for(int i=0;i<n;i++)if(!counts[i]){if(comma)out<<",";out<<i;comma=true;}
  out<<"],\"impossible_guards\":[";comma=false;
  for(int i=0;i<n;i++)if(counts[i]&&sites[i].op==2&&guards[i]!=3){
    if(comma)out<<",";
    out<<"{\"site\":"<<i<<",\"impossible\":\""<<(guards[i]==1?"positive":"zero")<<"\"}";comma=true;
  }
  out<<"],\"counts\":[";for(int i=0;i<n;i++){if(i)out<<",";out<<counts[i];}out<<"]}\n";
  std::cout<<"Joint abstract states: "<<queue.size()<<"\n";
  std::cout<<"Dead leaves:";for(int i=0;i<n;i++)if(!counts[i])std::cout<<" "<<i;std::cout<<"\n";
  for(int i=0;i<n;i++)if(counts[i]&&sites[i].op==2&&guards[i]!=3)
    std::cout<<"Impossible "<<(guards[i]==1?"positive":"zero")<<" at "<<i<<"\n";
}
