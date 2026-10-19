#include <bits/stdc++.h>
using namespace std;
struct Row { int w,d,z; };
struct Goal { int q,h,t; };
struct Case { int tape; vector<Goal> goals; };
Row table_[256][2]; bool exists_[256];
int main(int argc,char **argv) {
  if(argc<2) return 2;
  int L=argc>2?stoi(argv[2]):5, R=argc>3?stoi(argv[3]):5;
  int old_cap=argc>4?stoi(argv[4]):65, new_cap=argc>5?stoi(argv[5]):65;
  int W=L+R+1,N=1<<W,F=N-1;
  vector<int> states; vector<pair<int,int>> incoming[256];
  ifstream input(argv[1]); string line;
  while(getline(input,line)) {
    if(line.empty()||line[0]=='#') continue;
    int q,b,w,z;char d; stringstream ss(line);ss>>q>>b>>w>>d>>z;
    table_[q][b]={w,d=='R'?1:-1,z}; exists_[q]=true;
    incoming[z].push_back({q,b});
  }
  for(int q=0;q<256;q++) if(exists_[q]) states.push_back(q);
  vector<vector<int>> domain(256); vector<vector<bool>> seen(256,vector<bool>(N));
  queue<pair<int,int>> todo;
  for(int t=0;t<N;t++){seen[95][t]=true;todo.push({95,t});}
  while(!todo.empty()) {
    auto [q,t]=todo.front();todo.pop();domain[q].push_back(t);
    if(q==254) continue;
    Row a=table_[q][(t>>L)&1];
    int x=(t&~(1<<L))|(a.w<<L), u,v;
    if(a.d==1){u=x>>1;v=u|(1<<(W-1));}else{u=(x<<1)&F;v=u|1;}
    for(int y:{u,v}) if(!seen[a.z][y]){seen[a.z][y]=true;todo.push({a.z,y});}
  }
  string scope="inductive-all-tape";
  if(argc>6){
    scope="empirical-only";for(auto &ds:domain)ds.clear();
    ifstream dat(argv[6]);int q,t;while(dat>>q>>t)domain[q].push_back(t);
  }
  vector<Case> cases[256];long long totalcontexts=0;
  for(int q:states) {
    sort(domain[q].begin(),domain[q].end(),[&](int a,int b){return ((a*101)&F)<((b*101)&F);});
    for(int tape:domain[q]) {
      Case c{tape,{}};int h=0,s=q,t=tape;
      for(int k=0;k<old_cap;k++) {
        if(h< -L||h>R||s==254) break;
        Row a=table_[s][(t>>(L+h))&1];
        t=(t&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;s=a.z;
        c.goals.push_back({s,h,t});
      }
      cases[q].push_back(move(c));totalcontexts++;
    }
  }
  cerr<<"SCOPE "<<scope<<" L "<<L<<" R "<<R<<" caps "<<old_cap<<" "<<new_cap<<" contexts "<<totalcontexts<<endl;
  long long tested=0,candidates=0,contextchecks=0;auto start=chrono::steady_clock::now();
  for(int deleted:states) {
    if(deleted==95||incoming[deleted].empty()||cases[deleted].empty()) continue;
    int d=table_[incoming[deleted][0].first][incoming[deleted][0].second].d;
    bool uniform=true;for(auto [q,b]:incoming[deleted])if(table_[q][b].d!=d)uniform=false;
    if(!uniform)continue;
    int offset=-2*d;
    for(int retained:states) {
      if(retained==deleted) continue;
      tested++;bool valid=true;int maxnew=0,maxold=0;
      for(const auto &c:cases[deleted]) {
        contextchecks++;int q=retained,h=offset,t=c.tape;bool found=false;
        for(int k=1;k<=new_cap;k++) {
          if(h< -L||h>R||q==254)break;
          Row a=table_[q][(t>>(L+h))&1];
          if(a.z==deleted){a.z=retained;a.d=-a.d;}
          t=(t&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;q=a.z;
          for(int j=0;j<(int)c.goals.size();j++) {
            auto g=c.goals[j];if(g.q==deleted){g.q=retained;g.h+=offset;}
            if(q==g.q&&h==g.h&&t==g.t){found=true;maxnew=max(maxnew,k);maxold=max(maxold,j+1);break;}
          }
          if(found)break;
        }
        if(!found){valid=false;break;}
      }
      if(valid){candidates++;cout<<"SHIFT "<<deleted<<" "<<retained<<" "<<offset<<" MAX_OLD "<<maxold<<" MAX_NEW "<<maxnew<<" CONTEXTS "<<cases[deleted].size()<<endl;}
    }
  }
  cerr<<"FINISHED candidates "<<candidates<<" pairs "<<tested<<" contextchecks "<<contextchecks<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
