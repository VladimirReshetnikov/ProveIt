#include <bits/stdc++.h>
using namespace std;using U=uint64_t;
struct A{int w,d,n;bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
int main(int argc,char**argv){int K=stoi(argv[2]),B=stoi(argv[3]);array<A,2>r[3000];bool ex[3000]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;r[q][b]={w,d=='R'?1:-1,n};}
 map<pair<int,int>,vector<U>>pat;ifstream ps(argv[4]);U p;while(ps>>q>>p)pat[{q,(p>>K)&1}].push_back(p);
 for(auto &[key,pp]:pat){auto[q,b]=key;A old=r[q][b];cerr<<q<<","<<b<<" contexts "<<pp.size()<<"\n";
 for(int n:qs)for(int w:{0,1})for(int d:{-1,1}){A a{w,d,n};if(a==old)continue;bool ok=true;int maxst=0;
  for(U p:pp){int tq=old.n,th=old.d,cq=a.n,h=a.d;U tt=(p&~(U(1)<<K))|(U(old.w)<<K),t=(p&~(U(1)<<K))|(U(a.w)<<K);bool hit=false;
   for(int st=1;st<=B;st++){if(cq==tq&&h==th&&t==tt){hit=true;maxst=max(maxst,st);break;}if(h<-K||h>K||cq<0||cq>=3000||!ex[cq]||cq==q)break;A aa=r[cq][(t>>(h+K))&1];t=(t&~(U(1)<<(h+K)))|(U(aa.w)<<(h+K));h+=aa.d;cq=aa.n;}
   if(!hit){ok=false;break;}
  }
  if(ok)cout<<q<<' '<<b<<' '<<a.w<<' '<<a.d<<' '<<a.n<<' '<<maxst<<"\n";
 }
 }
}
