// Joint, not individually-neutral, three-row marker bootstrap repair search.
// New 122/0 checks the next bit; helper/1 restores the old bootstrap marker.
// Every accepted local rewrite must later pass all symbolic source contracts.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};struct C{int q,h,t;};
int main(int argc,char**argv){
 if(argc<4)return 2;int K=6,B=100;array<A,2>base[4096];bool ex[4096]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]={w,d=='R'?1:-1,n};}
 map<int,vector<int>>pat;ifstream p(argv[2]);int v;while(p>>q>>v)pat[q].push_back(v);
 set<int>box{0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 struct Case{int q,b,p;vector<C>ref;};vector<Case>cases[4096][2];
 for(auto &[q,ps]:pat)for(int t:ps){C c{q,0,t};Case z{q,(t>>K)&1,t,{}};for(int st=0;st<B&&abs(c.h)<=K&&ex[c.q];st++){A a=base[c.q][c.t>>(K+c.h)&1];c.t=(c.t&~(1<<(K+c.h)))|(a.w<<(K+c.h));c.h+=a.d;c.q=a.n;z.ref.push_back(c);}cases[q][z.b].push_back(move(z));}
 long long candidates=0,tests=0,hits=0;auto t0=chrono::steady_clock::now();
 for(int h:qs){if(h==122||box.count(h))continue;
 for(int target:qs)for(int wr:{0,1})for(int dir:{-1,1}){A a0{wr,dir,target};bool good=true;candidates++;
 vector<pair<int,int>>affected{{h,1},{122,0},{h,0}};
 for(auto [s,b]:affected){for(auto &z:cases[s][b]){tests++;C c{s,0,z.p};bool hit=false;
  for(int st=0;st<=B;st++){
   if(st)for(C r:z.ref)if(c.q==r.q&&c.h==r.h&&c.t==r.t){hit=true;break;}
   if(hit||st==B||abs(c.h)>K||!ex[c.q])break;
   int bit=c.t>>(K+c.h)&1;A a=base[c.q][bit];if(c.q==122&&bit==0)a={0,1,h};else if(c.q==h)a=bit?A{1,-1,16}:a0;
   c.t=(c.t&~(1<<(K+c.h)))|(a.w<<(K+c.h));c.h+=a.d;c.q=a.n;
  }
  if(!hit){good=false;break;}
 }if(!good)break;}
 if(good){hits++;cout<<"{\"helper\":"<<h<<",\"helper_zero\":["<<wr<<","<<dir<<","<<target<<"]}"<<endl;}
 }
 }
 cerr<<"candidates="<<candidates<<" localtests="<<tests<<" hits="<<hits<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
}
