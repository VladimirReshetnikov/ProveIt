// Adapted from prior zfc-beyond246/audit/search_flexible_spares.cpp.
// Extends the auxiliary hole to every retained row; exactly counted lazy pruning.
// Finite mutation screen, not a proof of nonhalting or state minimality.
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
struct Row {int w,d,q;};
using Table=std::array<std::array<Row,2>,256>;
struct Test {std::vector<int> v;int r;bool inc;};
int simulate(const Table& tab,const Test& x,int limit=1000) {
  constexpr int OFF=512,LIM=2048;
  std::array<unsigned char,LIM> a{};
  a[OFF-1]=1;
  int p=0,lo=-1,hi=-1;
  for (int i=0;i<int(x.v.size());++i) {
    for (int j=1+(i==x.r);j<x.v[i]+2;++j) a[OFF+p+j]=1;
    p+=x.v[i]+2;
  }
  hi=p-1;
  auto want=std::vector<int>(x.v.begin(),x.v.begin()+9);
  int q,h=0,exit,origin;
  if(x.inc) {q=73;exit=48;origin=0;++want[x.r];}
  else if(x.v[x.r]==0) {q=95;exit=112;origin=0;}
  else {q=95;exit=48;origin=1;--want[x.r];}
  for(int step=1;step<=limit;++step) {
    const auto row=tab[q][a[OFF+h]];
    if(row.q==-2)return 2; if(row.q<0)return false;
    if(a[OFF+h]==0 && row.q==q && ((row.d<0 && h<=lo) || (row.d>0 && h>=hi)))return false;
    a[OFF+h]=row.w;
    if(h<lo)lo=h;if(h>hi)hi=h;
    h+=row.d;q=row.q;
    if(h < -OFF || h >= LIM-OFF)return false;
    if(q==254 || q==255)return false;
    if(q!=exit || h!=origin-1)continue;
    if(origin && !a[OFF])return false;
    if(origin)a[OFF]=0;
    for(int k=lo;k<origin;++k)if(bool(a[OFF+k])!=(k==-1))return false;
    int last=hi;
    while(last>=origin && !a[OFF+last])--last;
    int k=origin,n=0;
    while(k<=last) {
      if(a[OFF+k])return false;
      ++k;
      int count=0;
      while(k<=last && a[OFF+k]){++k;++count;}
      if(!count)return false;
      if(n<9) {if(count-1!=want[n])return false;}
      else if(count!=2)return false;
      ++n;
    }
    return n>=10;
  }
  return false;
}
int main(int argc,char**argv) {
  if(argc!=2)return 2;
  Table t;
  for(auto &r:t)for(auto &a:r)a={0,0,-1};
  std::ifstream f(argv[1]);std::string line;
  std::vector<int> states;
  while(std::getline(f,line)) {
    if(line.empty()||line[0]=='#')continue;
    std::istringstream s(line);int q,a,w,r;char d;s>>q>>a>>w>>d>>r;
    t[q][a]={w,d=='R'?1:-1,r};
    if(!a&&q!=255)states.push_back(q);
  }
  std::vector<Row> actions;
  for(int w:{0,1})for(int d:{-1,1})for(int q:states)actions.push_back({w,d,q});
  std::vector<Test> tests;
  auto add=[&](int n,int r,bool inc,int style) {
    std::vector<int> v(9);
    for(int i=0;i<9;++i)v[i]=style==0?0:style==1?i:2;
    v.insert(v.end(),n,1);tests.push_back({v,r,inc});
  };
  add(1,0,false,0);add(1,0,true,0);add(2,8,false,0);add(2,8,true,0);
  for(int n:{1,2,5})for(int r:{0,2,8})for(int s:{0,1,2}) {
    add(n,r,true,s);add(n,r,false,s);
  }
  std::vector<std::pair<int,int>> aux; for(int q:states) for(int a:{0,1}) if(q!=75 || a!=0) aux.push_back({q,a});
  uint64_t total=0,passed=0;
  auto begun=std::chrono::steady_clock::now();
  #pragma omp parallel for num_threads(4) schedule(dynamic) reduction(+:total,passed)
  for(int auxidx=0;auxidx<int(aux.size());++auxidx) {
    auto [q,a]=aux[auxidx];
    std::ostringstream emitted;
    uint64_t local=0;
    Table cur=t;
    cur[255][0]=cur[255][1]={0,0,-1};
    for(auto main:actions) {
      cur[75][0]=main;cur[q][a]={0,0,-2};
      int at=0,result=0;
      for(;at<int(tests.size());++at) if((result=simulate(cur,tests[at]))!=1)break;
      if(at<int(tests.size()) && result==0) {total+=actions.size();continue;}
      for(auto extra:actions) {
        cur[q][a]=extra;++total;
        bool ok=true;
        for(int j=at;j<int(tests.size());++j)if(simulate(cur,tests[j])!=1){ok=false;break;}
        if(ok) {
          ++passed;++local;
          emitted<<"SURVIVOR 75 0 "<<main.w<<' '<<(main.d<0?'L':'R')<<' '<<main.q
                   <<" AUX "<<q<<' '<<a<<' '<<extra.w<<' '<<(extra.d<0?'L':'R')<<' '<<extra.q<<std::endl;
        }
      }
    }
    emitted<<"AUX_DONE "<<q<<' '<<a<<" survivors "<<local<<" recipes "<<actions.size()*actions.size()<<'\n';
    #pragma omp critical
    {std::cout<<emitted.str()<<std::flush;}
  }
  auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-begun).count();
  std::cout<<"FINITE_SCREEN_DONE total "<<total<<" survivors "<<passed<<" tests "<<tests.size()<<" elapsed_ms "<<ms<<'\n';
}
