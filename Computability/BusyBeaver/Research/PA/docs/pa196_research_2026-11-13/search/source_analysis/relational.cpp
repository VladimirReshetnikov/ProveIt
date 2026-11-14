#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

// Nine saturating trits and the sign of a chosen register difference.
// Exact 0, exact 1, and >=2; relation sign is negative / zero / positive.
int main(int argc,char**argv){
  if(argc!=2)throw std::runtime_error("graph.txt required");
  std::ifstream in(argv[1]);int n;in>>n;
  if(n!=3812)throw std::runtime_error("unexpected graph");
  std::vector<std::array<int,4>> graph(n);
  for(auto&r:graph){in>>r[0];if(r[0]==1)in>>r[1];if(r[0]==2)in>>r[1]>>r[2];if(r[0]==3)in>>r[1]>>r[2]>>r[3];if(!in)throw std::runtime_error("bad graph");}
  const int codes=19683,states=codes*3;std::array<int,9> power{};power[0]=1;for(int j=1;j<9;++j)power[j]=3*power[j-1];
  std::vector<std::array<uint8_t,9>> digits(codes);for(int c=0;c<codes;++c)for(int j=0;j<9;++j)digits[c][j]=c/power[j]%3;
  std::cout<<"[\n";
  for(int a=0;a<9;++a)for(int b=a+1;b<9;++b){
    std::vector<uint64_t> seen((uint64_t(n)*states+63)/64,0);std::vector<uint32_t> todo;
    auto add=[&](int pc,int c,int sign){
      int x=digits[c][a],y=digits[c][b];
      // Classes are disjoint ordered intervals. Only two tails can overlap.
      if(x!=y && sign!=(x<y?0:2))return;
      if(x==y && x<2 && sign!=1)return;
      uint32_t key=pc*states+sign*codes+c;uint64_t bit=uint64_t(1)<<(key%64);
      if(!(seen[key/64]&bit)){seen[key/64]|=bit;todo.push_back(key);}
    };
    add(25,2,a==0?2:1);
    for(size_t k=0;k<todo.size();++k){
      uint32_t key=todo[k];int pc=key/states,sign=key%states/codes,c=key%codes;auto r=graph[pc];
      if(r[0]==0)continue;if(r[0]==1){add(r[1],c,sign);continue;}
      int d=digits[c][r[1]],p=power[r[1]];
      if(r[0]==3 && !d){add(r[2],c,sign);continue;}
      int dir=r[0]==2?1:-1;
      int delta=(r[1]==a?dir:r[1]==b?-dir:0);
      int c1=r[0]==2?c+(d<2?p:0):c-p;
      auto relation=[&](int newc){
        int target=r[0]==2?r[2]:r[3];
        if(delta==0){add(target,newc,sign);return;}
        if(delta>0){
          if(sign==0){add(target,newc,0);add(target,newc,1);}
          else add(target,newc,2);
        }else{
          if(sign==2){add(target,newc,1);add(target,newc,2);}
          else add(target,newc,0);
        }
      };
      relation(c1);
      if(r[0]==3 && d==2)relation(c);
    }
    std::vector<int> reached(n,0),values(n,0);
    for(uint32_t key:todo){int pc=key/states,c=key%codes;reached[pc]++;if(graph[pc][0]==3)values[pc]|=1<<digits[c][graph[pc][1]];}
    if(a || b!=1)std::cout<<",\n";
    std::cout<<"{\"pair\":["<<a<<","<<b<<"],\"reachable_pairs\":"<<todo.size()<<",\"forced_zero\":[";
    bool first=true;for(int pc=0;pc<n;++pc)if(values[pc]==1){if(!first)std::cout<<",";first=false;std::cout<<pc;}
    std::cout<<"],\"forced_positive\":[";first=true;for(int pc=0;pc<n;++pc)if(values[pc] && !(values[pc]&1)){if(!first)std::cout<<",";first=false;std::cout<<pc;}
    std::cout<<"],\"unreachable\":[";first=true;for(int pc=0;pc<n;++pc)if(!reached[pc]){if(!first)std::cout<<",";first=false;std::cout<<pc;}
    std::cout<<"]}"<<std::flush;
  }
  std::cout<<"\n]\n";
}
