// Eliminate one control state by independently rerouting all external incoming rows.
// Exact positive joins, untouched surrounding tape, no patched row in macro interior.
// A miss is only a bounded result for the supplied finite invariant.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <tuple>
#include <vector>
using namespace std;
struct Tr { int w,d,t; };
struct C { int q,h,m; };
struct Test { int m; vector<C> goals; };
Tr T[1024][2]; vector<int> states, masks[1024];
int R,Start,Halt,Cap; bool Reentry;
bool changed[1024][2];
vector<C> old_trace(int p,int b0,int m,int dead) {
  int h=0,q=p; vector<C> out;
  for(int n=0;n<Cap;n++) {
    int j=h+R; if(j<0||j>2*R||q==Halt) break;
    int b=(m>>j)&1;
    if(n>0 && changed[q][b] && !(Reentry&&q==p&&b==b0)) break;
    Tr tr=T[q][b]; m=(m&~(1<<j))|(tr.w<<j);h+=tr.d;q=tr.t;
    if(q!=dead) out.push_back({q,h,m});
  }
  return out;
}
int test(Tr patch,const Test& x,int dead,int p,int b0) {
  if(x.goals.empty()) return 6;
  int q=-1,h=0,m=x.m;
  for(int n=0;n<Cap;n++) {
    int j=h+R; if(j<0||j>2*R) return 1;
    if(q==Halt) return 2;
    bool own=n>0&&q==p&&((m>>j)&1)==b0;
    if(n>0 && q==dead) return 3;
    if(n>0 && changed[q][(m>>j)&1]&&!(Reentry&&own)) return 4;
    Tr tr=(n==0||(Reentry&&own))?patch:T[q][(m>>j)&1];
    m=(m&~(1<<j))|(tr.w<<j);h+=tr.d;q=tr.t;
    if(q==dead) return 3;
    for(auto goal:x.goals) if(q==goal.q&&h==goal.h&&m==goal.m) return 0;
  }
  return 5;
}
int main(int argc,char**argv) {
  if(argc<2) return 2;
  ifstream f(argv[1]); int ns; f>>R>>Start>>Halt>>ns;
  Cap=argc>2?stoi(argv[2]):96;
  Reentry=argc>3&&stoi(argv[3]);
  for(int i=0;i<ns;i++) {
    int q,n;f>>q;states.push_back(q);
    for(int b=0;b<2;b++) f>>T[q][b].w>>T[q][b].d>>T[q][b].t;
    f>>n; for(int j=0;j<n;j++){int m;f>>m;masks[q].push_back(m);}
  }
  auto began=chrono::steady_clock::now();
  unsigned long long attempts=0,tests=0,reject[7]={}; int hits=0,rows_ok=0,rows_total=0;
  cout<<"{\"radius\":"<<R<<",\"cap\":"<<Cap<<",\"same_row_reentry\":"<<(Reentry?"true":"false")<<",\"states\":[";
  bool first=true;
  for(int dead:states) if(dead!=Start) {
    for(int q:states) for(int b=0;b<2;b++) changed[q][b]=q!=dead&&T[q][b].t==dead;
    vector<pair<int,int>> entries;
    for(int q:states) for(int b=0;b<2;b++) if(changed[q][b]) entries.push_back({q,b});
    int passed=0;
    if(!first) cout<<","; first=false;
    cout<<"{\"deleted\":"<<dead<<",\"incoming\":["; bool ef=true;
    for(auto [p,b]:entries) {
      rows_total++;
      vector<Test> cases;
      for(int m:masks[p]) if(((m>>R)&1)==b) cases.push_back({m,old_trace(p,b,m,dead)});
      stable_sort(cases.begin(),cases.end(),[](const Test&a,const Test&b){return a.goals.size()<b.goals.size();});
      vector<Tr> good;
      vector<int> targets=states;targets.push_back(Halt);
      for(int t:targets) if(t!=dead) for(int w=0;w<2;w++) for(int d:{-1,1}) {
        attempts++;Tr patch{w,d,t};bool ok=true;
        for(auto& c:cases){tests++;int fail=test(patch,c,dead,p,b);if(fail){reject[fail]++;ok=false;break;}}
        if(ok) good.push_back(patch);
      }
      if(!good.empty()){passed++;rows_ok++;}
      if(!ef)cout<<",";ef=false;
      cout<<"{\"row\":["<<p<<","<<b<<"],\"cases\":"<<cases.size()<<",\"patches\":[";
      for(int k=0;k<(int)good.size();k++){
        if(k)cout<<",";auto a=good[k];cout<<"["<<a.w<<","<<a.d<<","<<a.t<<"]";
      }cout<<"]}";
    }
    if(passed==(int)entries.size())hits++;
    cout<<"],\"passed\":"<<passed<<",\"total\":"<<entries.size()<<"}";
    cout.flush();
  }
  auto secs=chrono::duration<double>(chrono::steady_clock::now()-began).count();
  cout<<"],\"summary\":{\"attempts\":"<<attempts<<",\"case_tests\":"<<tests<<",\"rows_with_patch\":"<<rows_ok<<",\"total_rows\":"<<rows_total<<",\"state_eliminations\":"<<hits<<",\"seconds\":"<<secs<<"},\"rejections\":{";
  const char*labels[]={"","outside_window","halt_without_join","deleted_state","other_modified_row","fuel_exhausted","no_old_join_before_bound"};
  for(int i=1;i<=6;i++){if(i>1)cout<<",";cout<<"\""<<labels[i]<<"\":"<<reject[i];}
  cout<<"}}\n";
}
