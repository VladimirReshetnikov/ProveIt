#include <bits/stdc++.h>
using namespace std;
// Empirical discovery only. Any output needs a separate inductive proof.
struct Row { int w,d,z; };
struct Conf {int q,h,t;};
struct Case {int oldq,t; vector<Conf> goals;};
Row tab[256][2]; vector<int> states,inv[256]; vector<array<int,4>> incoming[256];
vector<Case> pre[256][2],cs[4];
int L=5,R=5,W=11,maskall=2047,oldcap=65,newcap=65;
int del,keep,helper,tag,entrydir; Row patch[4];
long long proposals=0,trials=0,hits=0;
int imageq(int q,int h,int t) {
 if(q!=del)return q;
 int pos=L+h-entrydir;if(pos<0||pos>=W)return -1;
 return ((t>>pos)&1)==tag?keep:helper;
}
int port(int q,int b) {return q==keep?b:q==helper?2+b:-1;}
bool testcase(Case const&c,int entry,int assigned) {
 int q=entry,h=0,t=c.t;
 for(int i=0;i<newcap;i++) {
  if(h<-L||h>R||q==254)return false;
  int b=(t>>(L+h))&1,p=port(q,b);
  if(p>=0 && !(assigned&(1<<p)))return true;
  Row a=p>=0?patch[p]:tab[q][b];
  t=(t&~(1<<(L+h)))|(a.w<<(L+h)); h+=a.d;q=a.z;
  if(q==del)q=a.w==tag?keep:helper; // all literal old incoming edges move right
  if(q<0)return false;
  for(auto const&g:c.goals)if(h==g.h && t==g.t && q==imageq(g.q,g.h,g.t))return true;
 }
 return false;
}
bool testport(int p,int assigned) {
 for(auto const&c:cs[p])if(!testcase(c,p<2?keep:helper,assigned))return false;
 return true;
}
bool alltests(int assigned) {
 for(int p=0;p<4;p++)if((assigned&(1<<p))&&!testport(p,assigned))return false;
 return true;
}
vector<Row> domains[4];vector<int> order;
void search(int index,int assigned) {
 if(index==4) {
  hits++;cout<<"SPLIT "<<del<<" KEEP "<<keep<<" TAG "<<tag<<" DIR "<<entrydir<<" HELPER "<<helper;
  for(auto a:patch)cout<<" "<<a.w<<" "<<a.d<<" "<<a.z;
  cout<<endl;return;
 }
 int p=order[index];
 for(auto a:domains[p]) {
  patch[p]=a;trials++;
  if(alltests(assigned|(1<<p)))search(index+1,assigned|(1<<p));
 }
}
int main(int argc,char**argv) {
 if(argc<3)return 2;ifstream f(argv[1]);string line;
 while(getline(f,line)) {
  if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;
  tab[q][b]={w,d=='R'?1:-1,z};incoming[z].push_back({q,b,w,d=='R'?1:-1});
  if(!b)states.push_back(q);
 }
 sort(states.begin(),states.end());ifstream v(argv[2]);int q,m;while(v>>q>>m)inv[q].push_back(m);
 for(int q:states)for(int m:inv[q]) {
  int b=(m>>L)&1;Case c{q,m,{}};int s=q,h=0,t=m;
  for(int i=0;i<oldcap;i++) {
   if(s==254||h<-L||h>R)break;int bb=(t>>(L+h))&1;Row a=tab[s][bb];
   t=(t&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;s=a.z;c.goals.push_back({s,h,t});
  }
  pre[q][b].push_back(move(c));
 }
 auto begun=chrono::steady_clock::now();
 for(int q:states) {
  if(q==95||q==96||incoming[q].empty())continue;
  set<int> tags,dirs;for(auto a:incoming[q]){tags.insert(a[2]);dirs.insert(a[3]);}
  if(dirs.size()!=1||tags.size()!=2)continue;entrydir=*dirs.begin();del=q;
  set<int> helpers(states.begin(),states.end());
  for(int r:helpers)if(r!=q&&r!=95&&r!=96&&r!=254) {
   helper=r;
   for(int p:states)if(p!=q&&p!=r&&p!=95&&p!=96) {
    keep=p;
    for(tag=0;tag<2;tag++) {
     // Prefer a fixed opposite old entry tag for p; the helper may have arbitrary callers.
     bool fixed=!incoming[p].empty();
     for(auto a:incoming[p])fixed&=a[3]==entrydir&&a[2]!=(tag);
     for(auto a:incoming[r])fixed&=a[3]==entrydir&&a[2]==tag;
     if(incoming[r].empty()||!fixed)continue;
     for(auto&c:cs)c.clear();
     for(int b=0;b<2;b++) {
      cs[b]=pre[p][b];cs[2+b]=pre[r][b];
      for(auto c:pre[q][b])cs[((c.t>>(L-entrydir))&1)==tag?b:2+b].push_back(move(c));
     }
     bool possible=true;
     for(int k=0;k<4;k++) {
      domains[k].clear();
      for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:states)if(z!=q) {
       patch[k]={w,d,z};
       if(testport(k,1<<k))domains[k].push_back(patch[k]);
      }
      if(domains[k].empty()){possible=false;break;}
     }
     proposals++;
     if(chrono::duration<double>(chrono::steady_clock::now()-begun).count()>600){cerr<<"TIME_BOUND proposals "<<proposals<<" combinations "<<trials<<" hits "<<hits<<endl;return 0;}
     if(possible) {
      order={0,1,2,3};sort(order.begin(),order.end(),[](int a,int b){return domains[a].size()<domains[b].size();});
      search(0,0);
     }
    }
   }
  }
  cerr<<"q "<<q<<" proposals "<<proposals<<" combinations "<<trials<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begun).count()<<endl;
 }
 cerr<<"DONE proposals "<<proposals<<" combinations "<<trials<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begun).count()<<endl;
}
