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
 long long combos=0,plaus=0;auto begin=chrono::steady_clock::now();
 for(int ai=0;ai<S;ai++){ca=states[ai];for(int bi=ai+1;bi<S;bi++){cb=states[bi];vector<Act> opts[2];
 for(int bit=0;bit<2;bit++) for(int w=0;w<2;w++)for(int d=0;d<2;d++)for(int n=0;n<=N;n++) {
  if(n==ca)continue;Act a{w,d,n};bool ok=true;
  for(int src:{ca,cb}){int c=0;for(const Ex&e:xs[src][bit]){if(!partial(src,bit,e,a)){ok=false;break;} if(++c>=10)break;}if(!ok)break;}
  if(ok)opts[bit].push_back(a);
 }
 if(opts[0].empty()||opts[1].empty())continue;plaus++;
 for(auto a0:opts[0])for(auto a1:opts[1]){combos++;bool ok=true;
  for(int src:{ca,cb})for(int bit=0;bit<2;bit++){if(!ok)break;int c=0;for(const Ex&e:xs[src][bit]){if(!full(src,bit,e,a0,a1)){ok=false;break;}if(++c>=15)break;}}
  if(!ok)continue;
  for(int src:{ca,cb})for(int bit=0;bit<2;bit++){if(!ok)break;for(const Ex&e:xs[src][bit])if(!full(src,bit,e,a0,a1)){ok=false;break;}}
  if(ok){cout<<"CAND "<<ca<<" "<<cb<<" "<<a0.w<<" "<<a0.d<<" "<<a0.n<<" "<<a1.w<<" "<<a1.d<<" "<<a1.n<<endl;}
 }
 } if(ai%10==0)cerr<<"progress "<<ai<<" pairs "<<plaus<<" choices "<<combos<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;}
 cerr<<"done "<<plaus<<" "<<combos<<endl;
}
