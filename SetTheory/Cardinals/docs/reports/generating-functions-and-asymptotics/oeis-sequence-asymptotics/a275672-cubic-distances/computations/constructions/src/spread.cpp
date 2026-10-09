#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <limits>
#include <random>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

// Stochastic tabu search. Heuristic failure is never an upper bound.
// Usage: ./search n k seed budget output.json
// Positive budget is seconds; negative budget is a deterministic iteration cap.
int main(int argc, char **argv) {
  if (argc != 6 && argc!=7) { std::cerr << "usage: adaptive n k seed seconds output.json [initial.json]\n"; return 2; }
  const int n=std::stoi(argv[1]), k=std::stoi(argv[2]), N=n*n*n;
  const uint64_t seed=std::stoull(argv[3]);
  const double requestedBudget=std::stod(argv[4]);
  const double budget=requestedBudget<0 ? std::numeric_limits<double>::infinity() : requestedBudget;
  const uint64_t iterationLimit=requestedBudget<0 ? uint64_t(-requestedBudget) : std::numeric_limits<uint64_t>::max();
  if(n<1 || n>148 || k<1 || k>N) {std::cerr<<"require 1<=n<=148 and 1<=k<=n^3\n";return 2;}
  const std::string output=argv[5];
  std::mt19937_64 gen(seed);
  auto rnd=[&](int a) { return int(gen()%a); };
  std::vector<int> X(N),Y(N),Z(N);
  for(int v=0;v<N;++v) { X[v]=v/(n*n); Y[v]=(v/n)%n; Z[v]=v%n; }
  auto dist=[&](int u,int v) {
    const int dx=X[u]-X[v],dy=Y[u]-Y[v],dz=Z[u]-Z[v];
    return dx*dx+dy*dy+dz*dz;
  };
  std::vector<uint16_t> ds(size_t(N)*k);
  const int D=3*(n-1)*(n-1)+1;
  std::vector<int> count(D),pts(k),bestPts(k),used(N),tabu(N),buf(k),conf(k),weight(D,1);
  const auto start=std::chrono::steady_clock::now();
  uint64_t iterations=0,restarts=0;
  int best=1000000;
  if(argc==7){
    std::ifstream fi(argv[6]);std::stringstream is;is<<fi.rdbuf();std::string s=is.str();size_t begin=s.find('[',s.find("\"points\"")),finish=begin;int depth=0;for(;finish<s.size();++finish){if(s[finish]=='[')++depth;else if(s[finish]==']' && --depth==0)break;}s=s.substr(begin,finish-begin+1);
    std::regex num("[0-9]+");std::sregex_iterator it(s.begin(),s.end(),num),end;std::vector<int>ns;
    for(;it!=end;++it)ns.push_back(std::stoi(it->str()));
    if(int(ns.size())!=3*k)return 3;
    for(int i=0;i<k;++i)bestPts[i]=(ns[3*i]*n+ns[3*i+1])*n+ns[3*i+2];
    best=0;for(int i=0;i<k;++i)for(int j=0;j<i;++j)best+=count[dist(bestPts[i],bestPts[j])]++;
  }
  auto elapsed=[&]() { return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count(); };
  auto save=[&](int energy) {
    std::ofstream out(output);
    out << "{\n  \"n\": "<<n<<", \"k\": "<<k<<", \"seed\": "<<seed
        <<", \"iterations\": "<<iterations<<", \"restarts\": "<<restarts
        <<", \"seconds\": "<<elapsed()<<", \"collision_pairs\": "<<energy<<", \"algorithm\": \"spread\",\n  \"points\": [";
    for(int i=0;i<k;++i) { int v=bestPts[i]; if(i)out<<",";out<<"["<<X[v]<<","<<Y[v]<<","<<Z[v]<<"]"; }
    out << "]\n}\n";
  };
  while(elapsed()<budget && iterations<iterationLimit) {
    ++restarts;
    std::fill(count.begin(),count.end(),0); std::fill(used.begin(),used.end(),0); std::fill(tabu.begin(),tabu.end(),0);std::fill(weight.begin(),weight.end(),1);
    if(best<1000000 && rnd(3)){pts=bestPts;for(int v:pts)used[v]=1;int changes=2+rnd(k/2);for(int i=0;i<changes;++i){int pos=rnd(k),v;used[pts[pos]]=0;do v=rnd(N);while(used[v]);pts[pos]=v;used[v]=1;}}
    else for(int i=0;i<k;++i) { int v; do v=rnd(N);while(used[v]);pts[i]=v;used[v]=1; }
    for(int v=0;v<N;++v)for(int i=0;i<k;++i)ds[size_t(v)*k+i]=dist(v,pts[i]);
    int energy=0;
    for(int i=0;i<k;++i)for(int j=0;j<i;++j)energy+=count[dist(pts[i],pts[j])]++;
    int stagnation=0;
    const int restartLimit=2500+rnd(15000);
    int localBest=energy;
    for(int step=1;step<=restartLimit && elapsed()<budget && iterations<iterationLimit;++step) {
      ++iterations;
      if(energy<best) {best=energy;bestPts=pts;save(best);std::cerr<<"n="<<n<<" k="<<k<<" best="<<best<<" it="<<iterations<<" t="<<elapsed()<<"\n";}
      if(energy==0) return 0;
      std::fill(conf.begin(),conf.end(),0);
      for(int i=0;i<k;++i)for(int j=0;j<i;++j) {
        int d=dist(pts[i],pts[j]);int c=(count[d]-1)*weight[d]; conf[i]+=c;conf[j]+=c;
      }
      int total=std::accumulate(conf.begin(),conf.end(),0), choose=rnd(total), pos=0;
      for(;pos<k-1 && choose>=conf[pos];++pos)choose-=conf[pos];
      // Periodic choice of any point helps leave local minima.
      if(rnd(30)==0)pos=rnd(k);
      int old=pts[pos]; used[old]=0;
      for(int j=0;j<k;++j) if(j!=pos)energy-=--count[dist(old,pts[j])];
      long long minimum=std::numeric_limits<long long>::max();int newv=old,ties=0;
      const int off=rnd(N);
      const bool spread = rnd(3)!=0;
      for(int vi=0;vi<N;++vi) {
        int v=(vi+off)%N;
        if(used[v] || v==old)continue;
        int cost=0,b=0,sum=0;
        const auto *row=&ds[size_t(v)*k];
        for(int j=0;j<k;++j) if(j!=pos) { int d=row[j];sum+=d;buf[b++]=d;cost+=weight[d]*count[d]++; }
        for(int j=0;j<b;++j)--count[buf[j]];
        if(tabu[v]>step && energy+cost>=best)continue;
        long long objective=1LL*cost*(k*D)+(spread ? k*D-sum : 0);
        if(objective<minimum) {minimum=objective;newv=v;ties=1;}
        else if(objective==minimum && rnd(++ties)==0)newv=v;
      }
      if(minimum==std::numeric_limits<long long>::max()) {newv=old;}
      pts[pos]=newv;used[newv]=1;
      for(int j=0;j<k;++j)if(j!=pos)energy+=count[dist(newv,pts[j])]++;
      for(int v=0;v<N;++v)ds[size_t(v)*k+pos]=dist(v,newv);
      tabu[old]=step+3+rnd(k+4);
      if(energy<localBest) {localBest=energy;stagnation=0;}else ++stagnation;
      if(step%50==0)for(int d=1;d<D;++d)if(count[d]>1)weight[d]+=1;
      if(step%1500==0)for(int d=1;d<D;++d)weight[d]=1+weight[d]/2;
      // Long unsuccessful walks are restarted; no conclusion follows.
      if(stagnation>3000+rnd(10000))break;
    }
  }
  save(best);
  return 1;
}
