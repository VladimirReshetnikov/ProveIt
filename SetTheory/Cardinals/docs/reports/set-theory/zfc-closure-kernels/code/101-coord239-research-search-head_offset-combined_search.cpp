// Extends the source80 offset/complement synthesis of ProveIt.
// Original algorithm attribution is retained in the report and NOTICE.
// New search: combine offset AND predecessor-bit complement; variable radius,
// blank/arbitrary seed, and old/new stuttering synchronization.
#include <algorithm>
#include <array>
#include <chrono>
#include <deque>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Act {int w,d,r;};
struct Conf {int q,h,t;};
struct Case {int t,h; vector<Conf> endpoints;};
Act O[256][2]; vector<int> dom[256],states; bool present[256];
int radius_,width_,mask_,limit_,del_,ret_,offset_,flipcell_,comp_;
vector<Case> cases_[2];
long long actions_=0,attempts_=0;
bool check(Act first,int bit) {
  for(const Case& c:cases_[bit]) {
    int q=ret_,h=c.h,t=c.t;
    bool good=false;
    for(int step=0;step<limit_;step++) {
      if(h < -radius_ || h > radius_ || q==254) break;
      int b=(t>>(h+radius_))&1;
      Act a;
      if(step==0) a=first;
      else {
        if(q==ret_)break;
        a=O[q][b];
        if(a.r==del_) {a.w^=comp_; if(offset_)a.d=-a.d; a.r=ret_;}
      }
      t=(t&~(1<<(h+radius_)))|(a.w<<(h+radius_));h+=a.d;q=a.r;
      for(auto e:c.endpoints)if(q==e.q&&h==e.h&&t==e.t){good=true;break;}
      if(good)break;
    }
    if(!good)return false;
  }
  return true;
}
int main(int argc,char**argv) {
  if(argc<7){cerr<<"table radius new_steps old_steps seed(arbitrary|blank) mode(offset|both|complement|plain) [profile]\n";return 2;}
  radius_=stoi(argv[2]);limit_=stoi(argv[3]);int old_steps=stoi(argv[4]);
  if(radius_<2||radius_>10||limit_<1||old_steps<1)return 2;
  width_=2*radius_+1;mask_=(1<<width_)-1;string seed=argv[5],mode=argv[6];
  ifstream f(argv[1]);string line;
  while(getline(f,line)) {
    if(line.empty()||line[0]=='#')continue;
    istringstream ss(line);int q,b,w,r;char d;ss>>q>>b>>w>>d>>r;
    O[q][b]={w,d=='R'?1:-1,r};present[q]=1;
  }
  for(int q=0;q<256;q++)if(present[q])states.push_back(q);
  vector<vector<bool>> seen(256,vector<bool>(1<<width_));deque<pair<int,int>> todo;
  int initial_count=seed=="blank"?1:mask_+1;
  for(int x=0;x<initial_count;x++){seen[95][x]=true;todo.emplace_back(95,x);}
  while(!todo.empty()) {
    auto[q,x]=todo.front();todo.pop_front();if(q==254)continue;
    Act a=O[q][(x>>radius_)&1];int y=(x&~(1<<radius_))|(a.w<<radius_);
    int z=a.d==1?y>>1:(y<<1)&mask_,edge=a.d==1?1<<(width_-1):1;
    for(int v:{z,z|edge})if(!seen[a.r][v]){seen[a.r][v]=true;todo.emplace_back(a.r,v);}
  }
  long long abstract_count=0;
  if(argc>7) {
    ifstream profile(argv[7]);int q,x;
    while(profile>>q>>x){dom[q].push_back(x);abstract_count++;}
  } else for(int q:states)for(int x=0;x<=mask_;x++)if(seen[q][x]){dom[q].push_back(x);abstract_count++;}
  cerr<<"abstract_count "<<abstract_count<<"\n";
  auto start=chrono::steady_clock::now();int survivors=0;
  for(int del:states) {
    if(argc>8&&del!=stoi(argv[8]))continue;
    if(del==95&&!(argc>8&&mode=="offset"))continue;
    set<int> directions;
    for(int q:states)for(int b=0;b<2;b++)if(q!=del&&O[q][b].r==del)directions.insert(O[q][b].d);
    if(directions.size()!=1&&mode!="plain")continue;
    del_=del;int entrydir=directions.empty()?1:*directions.begin();
    offset_=(mode=="complement"||mode=="plain")?0:-2*entrydir;
    comp_=(mode=="offset"||mode=="plain")?0:1;flipcell_=-entrydir;
    for(int ret:states) {
      if(ret==del)continue;ret_=ret;cases_[0].clear();cases_[1].clear();
      for(int s:{del,ret})for(int x:dom[s]) {
        int init=x^(s==del&&comp_?(1<<(radius_+flipcell_)):0);
        int ih=s==del?offset_:0;int bit=(init>>(radius_+ih))&1;
        Case c{init,ih,{}};
        int oq=s,oh=0,ot=x;
        for(int n=0;n<old_steps;n++) {
          if(oq==254||oh < -radius_ || oh > radius_)break;
          Act a=O[oq][(ot>>(oh+radius_))&1];
          ot=(ot&~(1<<(oh+radius_)))|(a.w<<(oh+radius_));oh+=a.d;oq=a.r;
          int nq=oq==del?ret:oq,nh=oh+(oq==del?offset_:0),nt=ot;
          if(oq==del&&comp_) {
            if(oh+flipcell_ < -radius_ || oh+flipcell_ > radius_)continue;
            nt^=1<<(radius_+oh+flipcell_);
          }
          c.endpoints.push_back({nq,nh,nt});
        }
        cases_[bit].push_back(move(c));
      }
      attempts_++;vector<Act> good[2];
      for(int b=0;b<2;b++) {
        if(b==1&&good[0].empty())break;
        for(int target:states)if(target!=del)for(int d:{-1,1})for(int w=0;w<2;w++) {
          actions_++;Act a{w,d,target};if(check(a,b))good[b].push_back(a);
        }
      }
      if(!good[0].empty()&&!good[1].empty())for(auto a:good[0])for(auto b:good[1]) {
        cout<<del<<" "<<ret<<" "<<offset_<<" "<<comp_<<" "<<a.w<<" "<<a.d<<" "<<a.r<<" "<<b.w<<" "<<b.d<<" "<<b.r<<"\n"<<flush;survivors++;
      }
    }
  }
  cerr<<"radius "<<radius_<<" new_steps "<<limit_<<" old_steps "<<old_steps<<" seed "<<seed<<" mode "<<mode<<" attempts "<<attempts_<<" actions "<<actions_<<" survivors "<<survivors<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
