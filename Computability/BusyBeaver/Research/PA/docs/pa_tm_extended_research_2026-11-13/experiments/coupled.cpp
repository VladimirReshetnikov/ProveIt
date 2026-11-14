#include <bits/stdc++.h>
using namespace std;
struct Act{int w,d,n;};struct Ex{array<int8_t,25>t;};
struct Cond{array<int8_t,25>t,g;int p,pg,ng;};
int N,R,S,ca,cb,qs,mask,fd,wmask;Act common;vector<array<Act,2>>rows;vector<array<vector<Ex>,2>>xs;vector<int>states;
int alias(int q){return q==ca?cb:q;}
Act known(int q,int b){if(q==cb){if(mask>>b&1)return{wmask>>b&1,fd,qs};return common;}return rows[q][b];}
bool good(const Cond&e,auto&t,int q,int p){return q==e.ng&&p==e.pg&&t==e.g;}
int prep(int src,int bit,const Ex&x,vector<Cond>*out){
 auto old=rows[src][bit];Cond e{x.t,x.t,R,R+(old.d?1:-1),alias(old.n)};e.g[R]=old.w;
 int q=alias(src),p=R;
 for(int k=0;k<80;k++){
  if(k&&good(e,e.t,q,p))return 1;
  if(p<0||p>=25||e.t[p]<0||q==N)return 0;
  if(q==qs){e.p=p;out[e.t[p]].push_back(e);return 1;}
  auto a=known(q,e.t[p]);e.t[p]=a.w;p+=a.d?1:-1;q=alias(a.n);
 }
 return 0;
}
int partial(const Cond&e,Act first){auto t=e.t;int p=e.p;t[p]=first.w;p+=first.d?1:-1;int q=alias(first.n);for(int k=0;k<80;k++){
 if(good(e,t,q,p))return 1;if(q==qs)return 2;if(p<0||p>=25||t[p]<0||q==N)return 0;
 auto a=known(q,t[p]);t[p]=a.w;p+=a.d?1:-1;q=alias(a.n);
 }return 0;}
bool full(const Cond&e,Act a0,Act a1){auto t=e.t;int p=e.p,q=qs;for(int k=0;k<160;k++){
 if(k&&good(e,t,q,p))return true;if(p<0||p>=25||t[p]<0||q==N)return false;
 auto a=q==qs?(t[p]?a1:a0):known(q,t[p]);t[p]=a.w;p+=a.d?1:-1;q=alias(a.n);
 }return false;}
int main(){ifstream in("experiments/contexts.dat");in>>N>>R>>S;states.resize(S);for(int&i:states)in>>i;rows.resize(N);xs.resize(N);for(auto&r:rows)for(auto&a:r)in>>a.w>>a.d>>a.n;for(auto&r:xs)for(auto&v:r){int n;in>>n;v.resize(n);for(auto&e:v)for(int8_t&b:e.t){int z;in>>z;b=z;}}
 ifstream ic("experiments/coupled_cases.dat");int nc;ic>>nc;long long combos=0;
 for(int i=0;i<nc;i++){ic>>ca>>cb>>mask>>fd>>wmask>>qs>>common.w>>common.d>>common.n;vector<Cond>con[2];bool ok=true;
 for(int src:{ca,cb,qs})for(int b=0;b<2;b++)for(auto&e:xs[src][b])if(!prep(src,b,e,con)){ok=false;break;}
 if(!ok)continue;vector<Act>opts[2];for(int b=0;b<2;b++)for(int w=0;w<2;w++)for(int d=0;d<2;d++)for(int n=0;n<=N;n++){if(n==ca)continue;Act a{w,d,n};bool ok=true;for(auto&e:con[b])if(!partial(e,a)){ok=false;break;}if(ok)opts[b].push_back(a);}
 for(auto a0:opts[0])for(auto a1:opts[1]){combos++;bool ok=true;for(int b=0;b<2;b++)for(auto&e:con[b])if(!full(e,a0,a1)){ok=false;break;}if(ok){cout<<ca<<" "<<cb<<" "<<mask<<" "<<fd<<" "<<wmask<<" "<<qs<<" "<<common.w<<" "<<common.d<<" "<<common.n<<" "<<a0.w<<" "<<a0.d<<" "<<a0.n<<" "<<a1.w<<" "<<a1.d<<" "<<a1.n<<endl;}}
 if(i%10==0)cerr<<"case "<<i<<" combos "<<combos<<endl;
 }
 cerr<<"done "<<nc<<" "<<combos<<endl;
}
