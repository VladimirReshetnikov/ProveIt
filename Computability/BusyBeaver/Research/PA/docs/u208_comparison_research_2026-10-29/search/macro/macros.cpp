#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <chrono>
using namespace std;
constexpr int W=81,C=40;
struct A{int w,d,r;};struct S{int q,h;array<signed char,W> tape;};
A t[400][2];vector<array<signed char,W>> cs[400];vector<int> states;int del,rep,lim;long long visited=0;int maxold=0,maxnew=0;
int val(const S&s,int p,const array<signed char,W>&o){return s.tape[p]>=0?s.tape[p]:o[p];}
bool match(const vector<S>&a,const vector<S>&b,const array<signed char,W>&o){
 for(int i=1;i<(int)a.size();i++)for(int j=1;j<(int)b.size();j++){
  if(a[i].q==254&&b[j].q==254){maxold=max(maxold,i);maxnew=max(maxnew,j);return true;}
  if(a[i].q==del||a[i].q!=b[j].q||a[i].h!=b[j].h)continue;
  bool same=true;for(int k=0;k<W;k++)if(val(a[i],k,o)!=val(b[j],k,o)){same=false;break;}
  if(same){maxold=max(maxold,i);maxnew=max(maxnew,j);return true;}
 }return false;
}
bool dfs(vector<S>a,vector<S>b,array<signed char,W>o,int turn,int &budget){
 visited++;if(--budget<0)return false;
 if(match(a,b,o))return true;
 int side=turn%2;auto &hist=side?b:a;S s=hist.back();
 if(s.q==254){if(a.back().q==254&&b.back().q==254)return true;return dfs(a,b,o,turn+1,budget);}
 if(hist.size()>lim||abs(s.h)>30)return false;
 int bit=val(s,s.h+C,o);
 if(bit<0){for(int v=0;v<2;v++){auto oo=o;oo[s.h+C]=v;if(!dfs(a,b,oo,turn,budget))return false;}return true;}
 A x=t[s.q][bit];if(side&&x.r==del)x.r=rep;
 s.tape[s.h+C]=x.w;s.h+=x.d;s.q=x.r;hist.push_back(s);
 return dfs(a,b,o,turn+1,budget);
}
int main(int argc,char**argv){lim=argc>2?atoi(argv[2]):16;ifstream in(argv[1]);int n;in>>n;
 for(int i=0;i<n;i++){int s,k;in>>s;states.push_back(s);in>>t[s][0].w>>t[s][0].d>>t[s][0].r>>t[s][1].w>>t[s][1].d>>t[s][1].r>>k;while(k--){array<signed char,W> c;c.fill(-1);int m;in>>m;while(m--){int p,b;in>>p>>b;if(abs(p)<C)c[p+C]=b;}cs[s].push_back(c);}}
 int hits=0,trials=0;auto start=chrono::steady_clock::now();
 for(int q:states){if(q==0)continue;del=q;
  for(int r:states){if(r==q)continue;rep=r;trials++;bool ok=true;maxold=maxnew=0;
   for(auto o:cs[q]){S a{q,0},b{r,0};a.tape.fill(-1);b.tape.fill(-1);int budget=3000;if(!dfs({a},{b},o,0,budget)){ok=false;break;}}
   if(ok){hits++;cout<<"HIT "<<q<<" -> "<<r<<" maxsteps "<<maxold<<","<<maxnew<<endl;}
  }
  if(q%20==0)cerr<<"progress "<<q<<" trials "<<trials<<" visited "<<visited<<" sec "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cout<<"DONE trials "<<trials<<" hits "<<hits<<" visited "<<visited<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
