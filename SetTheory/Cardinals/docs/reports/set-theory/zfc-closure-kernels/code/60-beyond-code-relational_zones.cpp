#include <algorithm>
#include <array>
#include <chrono>
#include <deque>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

// Finite, sound abstraction of nine natural counters by capped difference bounds.
// Matrix entry i,j denotes x_i-x_j <= b_ij, with x_0 fixed to zero.
constexpr int V=10, INF=1000000;
using Zone=std::array<int,V*V>;
struct Node { char op; int reg, a, b; };

bool close(Zone& z) {
  for(int k=0;k<V;k++) for(int i=0;i<V;i++) {
    if(z[i*V+k]==INF) continue;
    for(int j=0;j<V;j++) if(z[k*V+j]!=INF)
      z[i*V+j]=std::min(z[i*V+j],z[i*V+k]+z[k*V+j]);
  }
  for(int i=0;i<V;i++) if(z[i*V+i]<0) return false;
  return true;
}

bool transfer(Zone z, Node n, int branch, int cap, Zone& out) {
  if(!close(z)) return false;
  int r=n.reg+1;
  if(n.op=='D') {
    // branch 0: x_r=0; branch 1: x_r>=1, before decrement.
    if(branch==0) z[r*V]=std::min(z[r*V],0);
    else z[r]=std::min(z[r],-1);
    if(!close(z)) return false;
  }
  int delta=n.op=='I'?1:(n.op=='D'&&branch==1?-1:0);
  if(delta) for(int i=0;i<V;i++) if(i!=r) {
    if(z[r*V+i]!=INF) z[r*V+i]+=delta;
    if(z[i*V+r]!=INF) z[i*V+r]-=delta;
  }
  for(int i=0;i<V*V;i++) {
    int x=z[i];
    out[i]=x>cap?INF:std::max(-cap,x);
  }
  for(int i=0;i<V;i++) { out[i*V+i]=0; out[i]=std::min(out[i],0); }
  return true;
}

int main(int argc,char**argv) {
  if(argc!=4) {std::cerr<<"usage: relational_zones graph.txt cap output.txt\n";return 2;}
  std::ifstream in(argv[1]); int count,first; in>>count>>first;
  if(!in||count<=0) return 2;
  int cap=std::stoi(argv[2]); if(cap<1||cap>10000) return 2;
  std::vector<Node> g(count);
  for(auto& n:g) {in>>n.op>>n.reg>>n.a>>n.b; if(!in)return 2;}
  std::vector<Zone> zones(count); std::vector<bool> live(count),queued(count);
  zones[first].fill(0); live[first]=queued[first]=true;
  std::deque<int> queue{first}; long long pops=0,updates=0;
  auto began=std::chrono::steady_clock::now();
  while(!queue.empty()) {
    int s=queue.front();queue.pop_front();queued[s]=false;pops++;
    Node n=g[s];
    for(int b=0;b<(n.op=='D'?2:1);b++) {
      int t=b?n.b:n.a; if(t<0)continue;
      Zone post; if(!transfer(zones[s],n,b,cap,post))continue;
      bool changed=!live[t];
      if(!live[t]) {zones[t]=post;live[t]=true;}
      else for(int j=0;j<V*V;j++) if(post[j]>zones[t][j]) {zones[t][j]=post[j];changed=true;}
      if(changed) {updates++;if(!queued[t]){queue.push_back(t);queued[t]=true;}}
    }
  }
  // Explicit independent-of-worklist postfix check.
  for(int j=0;j<V*V;j++) if(zones[first][j]<0)return 3;
  int cases=0,disabled=0,edges=0;
  for(int s=0;s<count;s++) for(int b=0;b<(g[s].op=='D'?2:1);b++) {
    cases++; Zone post;
    if(!live[s]||!transfer(zones[s],g[s],b,cap,post)) {disabled++;continue;}
    int t=b?g[s].b:g[s].a;if(t<0)continue;edges++;
    if(!live[t])return 4;
    for(int j=0;j<V*V;j++)if(post[j]>zones[t][j])return 5;
  }
  std::ofstream out(argv[3]); out<<count<<' '<<cap<<' '<<pops<<' '<<updates<<'\n';
  for(int s=0;s<count;s++) {
    out<<(live[s]?1:0);
    if(live[s])for(int x:zones[s])out<<' '<<(x==INF?999999:x);
    out<<'\n';
  }
  auto secs=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::cout<<"{\"cap\":"<<cap<<",\"sites\":"<<count<<",\"live_sites\":"
    <<std::count(live.begin(),live.end(),true)<<",\"cases\":"<<cases
    <<",\"excluded_cases\":"<<disabled<<",\"postfix_edges\":"<<edges
    <<",\"worklist_pops\":"<<pops<<",\"updates\":"<<updates<<",\"seconds\":"<<secs<<"}\n";
}
