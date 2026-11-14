#include <bits/stdc++.h>
using namespace std;
struct Act {int w,d,n;};
struct Ex {array<int8_t,25>t;};
int N,R,S; vector<array<Act,2>> rows;vector<array<vector<Ex>,2>> xs; vector<int> states;
int ca,cb;
int alias(int q){return q==ca?cb:q;}
bool match(const array<int8_t,25>&t,const array<int8_t,25>&g,int q,int p,int ng,int pg) {
 return q==ng && p==pg && t==g;
}
int partial(int src,int bit,const Ex&e,Act first) {
 auto t=e.t,g=t;Act goal=rows[src][bit];g[R]=goal.w;int ng=alias(goal.n),pg=R+(goal.d?1:-1);
 int p=R,q=cb; t[p]=first.w;p+=first.d?1:-1;q=alias(first.n);
 for(int k=0;k<32;k++) {
  if(match(t,g,q,p,ng,pg)) return 1;
  if(q==cb) return 2;
  if(p<0||p>=25||t[p]<0||q==N)return 0;
  Act a=rows[q][t[p]];t[p]=a.w;p+=a.d?1:-1;q=alias(a.n);
 }
 return 0;
}
bool full(int src,int bit,const Ex&e,Act a0,Act a1) {
 auto t=e.t,g=t;Act goal=rows[src][bit];g[R]=goal.w;int ng=alias(goal.n),pg=R+(goal.d?1:-1);
 int p=R,q=cb;
 for(int k=0;k<120;k++) {
  if(k && match(t,g,q,p,ng,pg)) return true;
  if(p<0||p>=25||t[p]<0||q==N)return false;
  Act a=q==cb?(t[p]?a1:a0):rows[q][t[p]];t[p]=a.w;p+=a.d?1:-1;q=alias(a.n);
 }
 return false;
}
int main(){ifstream in("experiments/contexts.dat");in>>N>>R>>S;states.resize(S);for(int&i:states)in>>i;rows.resize(N);xs.resize(N);for(auto&r:rows)for(Act&a:r)in>>a.w>>a.d>>a.n;for(auto&r:xs)for(auto&v:r){int n;in>>n;v.resize(n);for(auto&e:v)for(int8_t&b:e.t){int z;in>>z;b=z;}}
 ca=-1;cb=-2;
 for(int q=0;q<N;q++)for(int b=0;b<2;b++) {
 vector<Act>okays;
 if(!xs[q][b].empty())for(int w=0;w<2;w++)for(int d=0;d<2;d++)for(int n=0;n<=N;n++) {
 Act a{w,d,n};bool ok=true;for(auto&e:xs[q][b])if(!partial(q,b,e,a)){ok=false;break;}if(ok)okays.push_back(a);
 }
 cout<<okays.size()<<"\n";for(auto a:okays)cout<<a.w<<" "<<a.d<<" "<<a.n<<"\n";
 }
}
