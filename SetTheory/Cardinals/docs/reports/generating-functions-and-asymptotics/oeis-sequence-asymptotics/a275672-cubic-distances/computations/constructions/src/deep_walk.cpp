#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <numeric>
#include <random>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

// Search for an extension of size k+1 by walking among valid k-point sets.
// Each large-neighborhood move deletes 4 or 5 points and refills them exactly.
// Failure of this heuristic is not an upper-bound certificate.
// Usage: feasible_walk n k seed budget input.json output.json [forbidden_distance]
// Positive budget is seconds; negative budget is a deterministic iteration cap.
int main(int argc,char **argv){
 if(argc!=7 && argc!=8){std::cerr<<"usage: feasible_walk n k seed budget input.json output.json [forbidden_distance]\n";return 2;}
 int n=std::stoi(argv[1]),k=std::stoi(argv[2]),N=n*n*n,M=3*(n-1)*(n-1)+1;
 int forbidden=argc==8?std::stoi(argv[7]):-1;
 if(n<1 || n>148 || k<1 || k>=N || forbidden>=M || forbidden==0)return 2;
 uint64_t seed=std::stoull(argv[3]);double requested=std::stod(argv[4]);
 double seconds=requested<0?std::numeric_limits<double>::infinity():requested;
 uint64_t limit=requested<0?uint64_t(-requested):std::numeric_limits<uint64_t>::max();
 std::mt19937_64 gen(seed);auto rnd=[&](int b){return int(gen()%b);};
 std::vector<int>X(N),Y(N),Z(N);for(int v=0;v<N;++v){X[v]=v/(n*n);Y[v]=(v/n)%n;Z[v]=v%n;}
 auto dist=[&](int u,int v){int dx=X[u]-X[v],dy=Y[u]-Y[v],dz=Z[u]-Z[v];return dx*dx+dy*dy+dz*dz;};
 std::ifstream in(argv[5]);std::stringstream ss;ss<<in.rdbuf();std::string input=ss.str();size_t begin=input.find('[',input.find("\"points\"")),finish=begin;int depth=0;for(;finish<input.size();++finish){if(input[finish]=='[')++depth;else if(input[finish]==']' && --depth==0)break;}input=input.substr(begin,finish-begin+1);
 std::regex number("[0-9]+");std::sregex_iterator it(input.begin(),input.end(),number),end;std::vector<int>nums,pts;
 for(;it!=end;++it)nums.push_back(std::stoi(it->str()));
 if(int(nums.size())!=3*k)return 3;
 for(int i=0;i<k;++i)pts.push_back((nums[3*i]*n+nums[3*i+1])*n+nums[3*i+2]);
 std::vector<int>count(M),indices(k),fixed,selected,cand,next,answer;
 if(forbidden>0)count[forbidden]=1;
 for(int i=0;i<k;++i)for(int j=0;j<i;++j){int d=dist(pts[i],pts[j]);if(!d || count[d]++)return 4;}
 uint64_t iterations=0,totalnodes=0,nodes=0,solutions=0,changes=0;
 auto start=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 int removed=0;
 std::function<bool(int)>dfs=[&](int from){
  ++nodes;
  if(nodes>200000)return false;
  if(int(selected.size())==removed){
   ++solutions;if(gen()%solutions==0){next=fixed;next.insert(next.end(),selected.begin(),selected.end());}
  }
  if(int(selected.size())==removed+1){answer=fixed;answer.insert(answer.end(),selected.begin(),selected.end());return true;}
  std::vector<int>buf(k+1);
  for(int ii=from;ii<int(cand.size());++ii){
   int v=cand[ii],len=0;bool good=true;
   for(int u:fixed){int d=dist(v,u);buf[len++]=d;if(count[d]++){good=false;break;}}
   if(good)for(int u:selected){int d=dist(v,u);buf[len++]=d;if(count[d]++){good=false;break;}}
   if(good){selected.push_back(v);if(dfs(ii+1))return true;selected.pop_back();}
   for(int j=0;j<len;++j)--count[buf[j]];
   if(nodes>200000)break;
  }
  return false;
 };
 auto save=[&](bool success){
  const auto &ps=success?answer:pts;std::ofstream out(argv[6]);
  out<<"{\"n\": "<<n<<", \"k\": "<<ps.size()<<", \"target\": "<<k+1<<", \"success\": "<<(success?"true":"false")<<", \"seed\": "<<seed<<", \"iterations\": "<<iterations<<", \"nodes\": "<<totalnodes<<", \"changes\": "<<changes<<", \"seconds\": "<<elapsed()<<", \"collision_pairs\": 0, \"algorithm\": \"feasible walk, deletion4/5\", \"forbidden_distance\": "<<forbidden<<", \"points\": [";
  for(int i=0;i<int(ps.size());++i){int v=ps[i];if(i)out<<",";out<<"["<<X[v]<<","<<Y[v]<<","<<Z[v]<<"]";}out<<"]}\n";
 };
 while(iterations<limit && elapsed()<seconds){
  ++iterations;removed=std::min(k,4+(rnd(3)==0));std::iota(indices.begin(),indices.end(),0);std::shuffle(indices.begin(),indices.end(),gen);
  fixed.clear();selected.clear();cand.clear();next.clear();std::fill(count.begin(),count.end(),0);
  if(forbidden>0)count[forbidden]=1;
  for(int i=removed;i<k;++i)fixed.push_back(pts[indices[i]]);
  for(int i=0;i<int(fixed.size());++i)for(int j=0;j<i;++j)++count[dist(fixed[i],fixed[j])];
  std::vector<int>buf(k+1);
  for(int v=0;v<N;++v){
   bool good=true;int len=0;
   for(int u:fixed){int d=dist(v,u);buf[len++]=d;if(!d || count[d]++){if(!d)++count[d];good=false;break;}}
   if(good)cand.push_back(v);for(int j=0;j<len;++j)--count[buf[j]];
  }
  std::shuffle(cand.begin(),cand.end(),gen);nodes=solutions=0;
  bool success=dfs(0);totalnodes+=nodes;
  if(success){save(true);std::cerr<<"SUCCESS n="<<n<<" k="<<k+1<<" iterations="<<iterations<<" seconds="<<elapsed()<<"\n";return 0;}
  if(!next.empty()){auto aa=next,bb=pts;std::sort(aa.begin(),aa.end());std::sort(bb.begin(),bb.end());if(aa!=bb)++changes;pts=next;}
 }
 save(false);return 1;
}
