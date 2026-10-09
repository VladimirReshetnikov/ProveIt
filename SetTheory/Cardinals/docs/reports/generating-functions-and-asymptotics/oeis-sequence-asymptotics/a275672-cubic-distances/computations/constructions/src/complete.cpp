#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <numeric>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

// Exhaustively refill r points after deleting r from an input configuration.
// Searches only neighborhoods of the supplied configuration, not the entire box.
// Usage: complete n k r input.json output.json
int main(int argc,char **argv) {
  if(argc!=6)return 2;
  const int n=std::stoi(argv[1]), k=std::stoi(argv[2]), r=std::stoi(argv[3]),N=n*n*n;
  const int M=3*(n-1)*(n-1)+1;
  std::ifstream in(argv[4]);std::stringstream ss;ss<<in.rdbuf();std::string input=ss.str();
  size_t begin=input.find('[',input.find("\"points\"")),finish=begin;int depth=0;for(;finish<input.size();++finish){if(input[finish]=='[')++depth;else if(input[finish]==']' && --depth==0)break;}input=input.substr(begin,finish-begin+1);
  std::regex number("[0-9]+");std::sregex_iterator it(input.begin(),input.end(),number),end;
  std::vector<int> nums,orig;for(;it!=end;++it)nums.push_back(std::stoi(it->str()));
  if(int(nums.size())!=3*k)return 3;
  for(int i=0;i<k;++i)orig.push_back((nums[3*i]*n+nums[3*i+1])*n+nums[3*i+2]);
  std::vector<int>X(N),Y(N),Z(N);for(int v=0;v<N;++v){X[v]=v/(n*n);Y[v]=(v/n)%n;Z[v]=v%n;}
  auto dist=[&](int u,int v){int dx=X[u]-X[v],dy=Y[u]-Y[v],dz=Z[u]-Z[v];return dx*dx+dy*dy+dz*dz;};
  std::vector<uint16_t>ds(size_t(N)*N);for(int u=0;u<N;++u)for(int v=0;v<N;++v)ds[size_t(u)*N+v]=dist(u,v);
  std::vector<int> deleted(k),fixed,selected,full,answer,count(M),cand,buf(k);
  uint64_t cores=0,validcores=0,nodes=0;
  const auto start=std::chrono::steady_clock::now();
  auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  std::function<bool(int,int)>fill=[&](int from,int need){
    ++nodes;
    if(need==0){answer=fixed;answer.insert(answer.end(),selected.begin(),selected.end());return true;}
    std::vector<int> localbuf(k);
    for(int ii=from;ii+need<=int(cand.size());++ii){
      int v=cand[ii],len=0;bool good=true;
      for(int u:fixed){int d=ds[size_t(v)*N+u];localbuf[len++]=d;if(count[d]++){good=false;break;}}
      if(good)for(int u:selected){int d=ds[size_t(v)*N+u];localbuf[len++]=d;if(count[d]++){good=false;break;}}
      if(good){selected.push_back(v);if(fill(ii+1,need-1))return true;selected.pop_back();}
      for(int j=0;j<len;++j)--count[localbuf[j]];
    }
    return false;
  };
  auto core=[&](){
    ++cores;std::fill(count.begin(),count.end(),0);fixed.clear();selected.clear();cand.clear();
    for(int i=0;i<k;++i)if(!deleted[i])fixed.push_back(orig[i]);
    for(int i=0;i<int(fixed.size());++i)for(int j=0;j<i;++j)if(count[ds[size_t(fixed[i])*N+fixed[j]]]++)return false;
    ++validcores;
    for(int v=0;v<N;++v){
      bool good=true;int len=0;
      for(int u:fixed){int d=ds[size_t(v)*N+u];buf[len++]=d;if(d==0 || count[d]++){if(d==0)++count[d];good=false;break;}}
      if(good)cand.push_back(v);
      for(int j=0;j<len;++j)--count[buf[j]];
    }
    return fill(0,r);
  };
  std::function<bool(int,int)>choose=[&](int from,int rem){
    if(rem==0)return core();
    for(int i=from;i+rem<=k;++i){deleted[i]=1;if(choose(i+1,rem-1))return true;deleted[i]=0;}return false;
  };
  bool found=choose(0,r);
  std::cerr<<"cores="<<cores<<" valid="<<validcores<<" nodes="<<nodes<<" time="<<elapsed()<<" found="<<found<<"\n";
  if(found){std::ofstream out(argv[5]);out<<"{\"n\": "<<n<<", \"k\": "<<k<<", \"method\": \"exact neighborhood completion\", \"deleted\": "<<r<<", \"source\": \""<<argv[4]<<"\", \"seconds\": "<<elapsed()<<", \"collision_pairs\": 0, \"points\": [";for(int i=0;i<k;++i){int v=answer[i];if(i)out<<",";out<<"["<<X[v]<<","<<Y[v]<<","<<Z[v]<<"]";}out<<"]}\n";return 0;}
  return 1;
}
