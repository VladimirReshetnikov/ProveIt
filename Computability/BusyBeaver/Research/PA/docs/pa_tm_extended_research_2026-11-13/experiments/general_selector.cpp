#include <bits/stdc++.h>
using namespace std;
struct Act {int w,d,n; bool operator<(const Act&a)const{return tie(w,d,n)<tie(a.w,a.d,a.n);} bool operator==(const Act&a)const{return tie(w,d,n)==tie(a.w,a.d,a.n);}};
struct Ex {array<int8_t,25> t;};
int N,R,S;vector<array<Act,2>> rows;vector<array<vector<Ex>,2>> xs;vector<int>states;vector<array<set<Act>,2>> repl;
int ca,cb;int alias(int q){return q==ca?cb:q;}
bool reaches(int src,int bit,const Ex&e,int fw,int fd,Act sel,int sidebit) {
 auto t=e.t,g=t;auto old=rows[src][bit];g[R]=old.w;int ng=alias(old.n),pg=R+(old.d?1:-1);
 t[R]=fw;int p=R+(fd?1:-1);if(t[p]!=sidebit)return true;
 t[p]=sel.w;p+=sel.d?1:-1;int q=alias(sel.n);
 for(int k=0;k<40;k++) {
  if(q==ng&&p==pg&&t==g)return true;
  if(p<0||p>=25||t[p]<0||q==N)return false;
  auto a=rows[q][t[p]];t[p]=a.w;p+=a.d?1:-1;q=alias(a.n);
 }
 return false;
}
int main(){ifstream in("experiments/contexts.dat");in>>N>>R>>S;states.resize(S);for(int&i:states)in>>i;rows.resize(N);xs.resize(N);repl.resize(N);for(auto&r:rows)for(Act&a:r)in>>a.w>>a.d>>a.n;for(auto&r:xs)for(auto&v:r){int n;in>>n;v.resize(n);for(auto&e:v)for(int8_t&b:e.t){int z;in>>z;b=z;}}
 ifstream ia("experiments/actions.dat");for(int q=0;q<N;q++)for(int b=0;b<2;b++){int c;ia>>c;repl[q][b].insert(rows[q][b]);while(c--){Act a;ia>>a.w>>a.d>>a.n;repl[q][b].insert(a);}}
 long long cases=0,possible=0,edges=0;auto begin=chrono::steady_clock::now();
 for(int ai=0;ai<S;ai++){ca=states[ai];for(int bi=ai+1;bi<S;bi++){cb=states[bi];vector<Act>common[2];for(int b=0;b<2;b++)set_intersection(repl[ca][b].begin(),repl[ca][b].end(),repl[cb][b].begin(),repl[cb][b].end(),back_inserter(common[b]));
 for(int mask=1;mask<4;mask++){if((mask==1&&common[1].empty())||(mask==2&&common[0].empty()))continue;
 for(int fd=0;fd<2;fd++)for(int wmask=0;wmask<4;wmask++){if(wmask&~mask)continue;cases++;
 bool known=true;for(int src:{ca,cb})for(int b=0;b<2;b++)if(mask>>b&1)for(auto&e:xs[src][b])if(e.t[R+(fd?1:-1)]<0){known=false;break;}if(!known)continue;
 vector<tuple<int,int,const Ex*>> criteria[2];for(int src:{ca,cb})for(int b=0;b<2;b++)if(mask>>b&1)for(auto&e:xs[src][b])criteria[e.t[R+(fd?1:-1)]].push_back({src,b,&e});if(criteria[0].empty()||criteria[1].empty())continue;
 vector<Act>possible[2];for(int sidebit=0;sidebit<2;sidebit++)for(int w=0;w<2;w++)for(int d=0;d<2;d++)for(int n=0;n<=N;n++){if(n==ca||n==cb)continue;Act sel{w,d,n};bool ok=true;
 for(auto[src,b,e]:criteria[sidebit]){if(!reaches(src,b,*e,wmask>>b&1,fd,sel,sidebit)){ok=false;break;}}
 if(ok)possible[sidebit].push_back(sel);
 }
 if(possible[0].empty()||possible[1].empty())continue;
 for(auto a0:possible[0])for(auto a1:possible[1]){edges++;cout<<ca<<" "<<cb<<" "<<mask<<" "<<fd<<" "<<wmask<<" "<<a0.w<<" "<<a0.d<<" "<<a0.n<<" "<<a1.w<<" "<<a1.d<<" "<<a1.n<<" ";for(int b=0;b<2;b++)if(!(mask>>b&1)) {auto a=common[b][0];cout<<a.w<<" "<<a.d<<" "<<a.n;}cout<<endl;}
 }
 }
 } if(ai%10==0)cerr<<"progress "<<ai<<" cases "<<cases<<" edges "<<edges<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;}
 cerr<<"done "<<cases<<" "<<edges<<endl;
}
