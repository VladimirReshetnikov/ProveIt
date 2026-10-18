// Exact literal finite screening. A survivor still needs an unbounded proof.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
struct Row {int w=0,d=0,t=-1;};
struct Case {bool halt;int head;std::vector<int> initial,target;};
struct Group {int q,p,b;std::vector<int> cases;};
constexpr int BOUND=20032,ORIGIN=10016,FUEL=10000;
std::array<std::array<Row,2>,256> table;
std::array<unsigned char,BOUND> tape;
const char* failure_reason="";
bool run(const Case& c,int removed) {
  tape.fill(0);for(int p:c.initial)tape[ORIGIN+p]=1;
  int q=96,h=ORIGIN,lo=ORIGIN-1,hi=ORIGIN+160,visits=0;
  for(int step=0;step<FUEL;++step){
    if(q==removed){failure_reason="removed_state";return false;}
    Row r=table[q][tape[h]];if(r.t<0){failure_reason="missing_row";return false;}
    tape[h]=r.w;h+=r.d;q=r.t;
    lo=std::min(lo,h);hi=std::max(hi,h);
    if(h<1||h>=BOUND-1){failure_reason="tape_bound";return false;}
    if(q==254){failure_reason="unexpected_halt";return c.halt;}
    if(q==96){
      if(!c.halt&&h==ORIGIN+c.head){
        int j=0;bool ok=true;
        for(int p=lo;p<=hi;++p)if(tape[p]){
          if(j>=int(c.target.size())||p-ORIGIN!=c.target[j++]){ok=false;break;}
        }
        if(ok&&j==int(c.target.size()))return true;
      }
      if(++visits>15){failure_reason="dispatcher_budget";return false;}
    }
  }
  failure_reason="step_budget";return false;
}
int main(int argc,char**argv){
  if(argc!=4&&argc!=5)throw std::runtime_error("table cases members [rejections.jsonl]");
  std::ifstream ft(argv[1]),fc(argv[2]),fm(argv[3]);int n;
  std::ofstream rejections;if(argc==5)rejections.open(argv[4]);
  ft>>n;std::vector<int>states;
  while(n--){int q,b,w,d,t;ft>>q>>b>>w>>d>>t;table[q][b]={w,d,t};if(!b)states.push_back(q);}
  fc>>n;std::vector<Case>cases(n);
  for(auto&c:cases){int h,sz;fc>>h>>c.head>>sz;c.halt=h;c.initial.resize(sz);for(int&p:c.initial)fc>>p;fc>>sz;c.target.resize(sz);for(int&p:c.target)fc>>p;}
  fm>>n;std::vector<Group>groups(n);
  for(auto&g:groups){int sz;fm>>g.q>>g.p>>g.b>>sz;g.cases.resize(sz);for(int&i:g.cases)fm>>i;}
  long long tried=0,survived=0,literalsuites=0;auto began=std::chrono::steady_clock::now();
  for(const auto&g:groups){
    Row original=table[g.p][g.b];long long gs=0;
    for(int w:{0,1})for(int d:{-1,1})for(int t:states)if(t!=g.q){
      ++tried;table[g.p][g.b]={w,d,t};bool ok=true;
      for(int id:g.cases){++literalsuites;if(!run(cases[id],g.q)){
        ok=false;
        if(rejections)rejections<<"["<<g.q<<','<<g.p<<','<<g.b<<','<<w<<','<<d<<','<<t<<','<<id<<",\""<<failure_reason<<"\"]\n";
        break;
      }}
      if(ok){++survived;++gs;std::cout<<"{\"deleted\":"<<g.q<<",\"source\":["<<g.p<<','<<g.b<<"],\"action\":["<<w<<','<<d<<','<<t<<"],\"cases\":"<<g.cases.size()<<"}\n"<<std::flush;}
    }
    table[g.p][g.b]=original;
    std::cerr<<"state "<<g.q<<" survivors "<<gs<<"\n";
  }
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::cerr<<"{\"recipes\":"<<tried<<",\"survivors\":"<<survived<<",\"case_runs\":"<<literalsuites<<",\"seconds\":"<<seconds<<"}\n";
}
