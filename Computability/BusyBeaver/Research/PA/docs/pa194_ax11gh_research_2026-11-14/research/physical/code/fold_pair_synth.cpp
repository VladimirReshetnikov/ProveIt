#include <bits/stdc++.h>
using namespace std;using U=uint64_t;
struct A {int w,d,n; bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
struct C {int q,h;U t;bool operator==(const C&o)const{return q==o.q&&h==o.h&&t==o.t;}};
int main(int argc,char**argv){
 int K=stoi(argv[2]),B=stoi(argv[3]),keep=stoi(argv[5]),rem=stoi(argv[6]);
 array<A,2> old[3000],base[3000],r[3000];bool ex[3000]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n){if(!ex[q]&&q!=rem)qs.push_back(q);ex[q]=true;old[q][b]={w,d=='R'?1:-1,n};}
 for(int q:qs)for(int b:{0,1}){base[q][b]=old[q][b];if(base[q][b].n==rem)base[q][b].n=keep;r[q][b]=base[q][b];}
 auto step=[&](C c,bool orig){A a=(orig?old:r)[c.q][(c.t>>(c.h+K))&1];return C{a.n,c.h+a.d,(c.t&~(U(1)<<(c.h+K)))|(U(a.w)<<(c.h+K))};};
 vector<pair<C,vector<C>>>tests;ifstream ps(argv[4]);U p;
 while(ps>>q>>p){b=(p>>K)&1;if((q!=keep&&q!=rem)||b!=0)continue;C start{keep,0,p},v{q,0,p};vector<C>ref;
  for(int st=0;st<B;st++){v=step(v,true);C v2=v;if(v2.q==rem)v2.q=keep;ref.push_back(v2);if(v.h<-K||v.h>K||v.q<0||v.q>=3000||!ex[v.q]||v.q==keep||v.q==rem)break;}
  tests.push_back({start,ref});
 }
 vector<A>acts;for(int n:qs)for(int w:{0,1})for(int d:{-1,1})acts.push_back({w,d,n});
 long long count=0,hits=0;cerr<<"tests "<<tests.size()<<" acts "<<acts.size()<<"\n";
 for(A a:acts){r[keep][0]=a;C v=tests[0].first;set<pair<int,int>>candidates;vector<C>seen;
  for(int st=0;st<B;st++){if(v.h<-K||v.h>K||v.q<0||v.q>=3000||!ex[v.q]||v.q==rem||find(seen.begin(),seen.end(),v)!=seen.end())break;seen.push_back(v);int b=(v.t>>(v.h+K))&1;if(v.q!=keep||b!=0)candidates.insert({v.q,b});v=step(v,false);}
  for(auto[q2,b2]:candidates)for(A aa:acts){if(aa==base[q2][b2])continue;r[q2][b2]=aa;count++;bool ok=true;int maxst=0;
   for(auto&[start,ref]:tests){C v=start;bool hit=false;vector<C>seen;
    for(int st=1;st<=B;st++){v=step(v,false);if(find(ref.begin(),ref.end(),v)!=ref.end()){hit=true;maxst=max(maxst,st);break;}if(v.h<-K||v.h>K||v.q<0||v.q>=3000||!ex[v.q]||v.q==rem||find(seen.begin(),seen.end(),v)!=seen.end())break;seen.push_back(v);}
    if(!hit){ok=false;break;}
   }
   if(ok){hits++;cout<<keep<<" 0 "<<a.w<<' '<<a.d<<' '<<a.n<<" | "<<q2<<' '<<b2<<' '<<aa.w<<' '<<aa.d<<' '<<aa.n<<" | "<<maxst<<'\n';}
   r[q2][b2]=base[q2][b2];
  }
 }
 cerr<<"checked "<<count<<" hits "<<hits<<"\n";
}
