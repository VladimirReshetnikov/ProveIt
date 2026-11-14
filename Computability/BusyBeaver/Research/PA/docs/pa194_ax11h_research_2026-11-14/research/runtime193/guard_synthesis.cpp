#include <bits/stdc++.h>
using namespace std;using U=uint64_t;
struct A{int w,d,n;bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
struct C{int q,h;U t;bool operator==(const C&o)const{return q==o.q&&h==o.h&&t==o.t;}};
int main(int argc,char**argv){int K=stoi(argv[2]),B=stoi(argv[3]),q1=stoi(argv[5]),b1=stoi(argv[6]);array<A,2>r[3000],old[3000];bool ex[3000]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;old[q][b]=r[q][b]={w,d=='R'?1:-1,n};}
 vector<pair<C,vector<C>>> tests;ifstream ps(argv[4]);U p;
 auto step=[&](C c,bool orig){A a=(orig?old:r)[c.q][(c.t>>(c.h+K))&1];return C{a.n,c.h+a.d,(c.t&~(U(1)<<(c.h+K)))|(U(a.w)<<(c.h+K))};};
 while(ps>>q>>p){b=(p>>K)&1;if(q!=q1||b!=b1)continue;C start{q,0,p},v=start;vector<C>ref;
  for(int st=0;st<64;st++){v=step(v,true);ref.push_back(v);if(v.h<-K||v.h>K||v.q<0||v.q>=3000||!ex[v.q])break;}
  tests.push_back({start,ref});
 }
 int successes=0;long long count=0;vector<A>acts;for(int n:qs)for(int w:{0,1})for(int d:{-1,1})acts.push_back({w,d,n});set<int>boxes{0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 cerr<<"tests "<<tests.size()<<" acts "<<acts.size()<<"\n";
 for(A a:acts){if(a==old[q1][b1])continue;r[q1][b1]=a;auto v=tests[0].first;set<pair<int,int>> candidates;vector<C>seen;
  for(int st=0;st<B;st++){if(v.h<-K||v.h>K||v.q<0||v.q>=3000||!ex[v.q]||find(seen.begin(),seen.end(),v)!=seen.end())break;seen.push_back(v);int b=(v.t>>(v.h+K))&1;if(!boxes.count(v.q)&&(v.q!=q1||b!=b1))candidates.insert({v.q,b});v=step(v,false);}
  for(auto [q2,b2]:candidates)for(A b:acts){if(b==old[q2][b2])continue;r[q2][b2]=b;count++;bool ok=true;int maxst=0;
   for(auto &[start,ref]:tests){C v=start;bool hit=false;vector<C>seen;
    for(int st=1;st<=B;st++){v=step(v,false);if(find(ref.begin(),ref.end(),v)!=ref.end()){hit=true;maxst=max(maxst,st);break;}if(v.h<-K||v.h>K||v.q<0||v.q>=3000||!ex[v.q]||find(seen.begin(),seen.end(),v)!=seen.end())break;seen.push_back(v);}
    if(!hit){ok=false;break;}
   }
   if(ok){successes++;cout<<q1<<' '<<b1<<' '<<a.w<<' '<<a.d<<' '<<a.n<<" | "<<q2<<' '<<b2<<' '<<b.w<<' '<<b.d<<' '<<b.n<<" | "<<maxst<<'\n';}
   r[q2][b2]=old[q2][b2];
  }
 }
 cerr<<"checked "<<count<<" successes "<<successes<<"\n";
}
