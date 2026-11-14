// Research synthesis: quotient two controls with at most one additional row rewrite.
// Every accepted local window is checked against the original exact one-step target.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;bool operator==(A const&o)const{return w==o.w&&d==o.d&&n==o.n;}bool operator<(A const&o)const{return tie(w,d,n)<tie(o.w,o.d,o.n);}};
struct O{A a;int pq=-1,pb=-1;A pa{};};
int main(int argc,char**argv){if(argc<5)return 2;int K=stoi(argv[3]),BD=stoi(argv[4]);array<A,2>rows[5000];bool ex[5000]={};vector<int>states;ifstream f(argv[1]);int q,b,w,n;char dr;while(f>>q>>b>>w>>dr>>n){if(!ex[q])states.push_back(q);ex[q]=true;rows[q][b]={w,dr=='R'?1:-1,n};}
 vector<int> pat[5000];ifstream pf(argv[2]);int p;while(pf>>q>>p)pat[q].push_back(p);
 set<int> boxes={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 map<A,vector<int>> has[2];for(int q:states)for(int b:{0,1})has[b][rows[q][b]].push_back(q);
 int leftmask[5000][2]={};for(int q:states)for(int p:pat[q])leftmask[q][p>>K&1]|=1<<(p>>(K-1)&1);
 long long pairs=0,proposals=0,trials=0,hits=0;auto t=chrono::steady_clock::now();
 for(int a:states)for(int keep:states){if(a>=keep||boxes.count(a)||boxes.count(keep))continue;pairs++;
  vector<O>opts[2];
  for(int bit:{0,1}){
   if(rows[a][bit]==rows[keep][bit])opts[bit].push_back({rows[a][bit]});
   int aa=leftmask[a][bit],bb=leftmask[keep][bit];
   if(!(aa==1&&bb==2)&&!(aa==2&&bb==1))continue;
   A want[2];want[aa==1?0:1]=rows[a][bit];want[bb==1?0:1]=rows[keep][bit];
   for(int h:states){if(h==a||h==keep)continue;bool good[2];for(int side:{0,1}){A act=rows[h][side];good[side]=act.w==side&&act.d==1&&act.n!=a&&act.n!=keep&&ex[act.n]&&rows[act.n][bit]==want[side];}
    if(good[0]&&good[1])opts[bit].push_back({{bit,-1,h}});
    if(boxes.count(h))continue;
    for(int side:{0,1})if(good[1-side]&&!good[side])for(int dest:has[bit][want[side]]){if(dest==a||dest==keep)continue;A pa{side,1,dest};if(pa==rows[h][side])continue;opts[bit].push_back({{bit,-1,h},h,side,pa});}
   }
  }
  if(opts[0].empty()||opts[1].empty())continue;
  for(O z:opts[0])for(O o:opts[1]){
   if(z.pq<0&&o.pq<0)continue;
   if(z.pq>=0&&o.pq>=0&&!(z.pq==o.pq&&z.pb==o.pb&&z.pa==o.pa))continue;
   O patch=z.pq>=0?z:o;array<A,2>acts{z.a,o.a};proposals++;
   auto check=[&](int old,int tape)->bool{
    int bit=tape>>K&1;A goal=rows[old][bit];int tq=goal.n==a?keep:goal.n,th=goal.d,tt=(tape&~(1<<K))|(goal.w<<K);int q=old==a?keep:old,h=0,t=tape;
    for(int j=0;j<=BD;j++){
     if(j&&q==tq&&h==th&&t==tt)return true;
     if(j==BD||h<-K||h>K||q<0||q>=5000||!ex[q])return false;
     int b=t>>(h+K)&1;A x=q==keep?acts[b]:(q==patch.pq&&b==patch.pb?patch.pa:rows[q][b]);
     t=(t&~(1<<(h+K)))|(x.w<<(h+K));h+=x.d;q=x.n==a?keep:x.n;
    }return false;
   };
   // Helper windows most often rule out a speculative provider patch.
   bool ok=true;for(int p:pat[patch.pq])if((p>>K&1)==patch.pb){trials++;if(!check(patch.pq,p)){ok=false;break;}}
   if(ok)for(int q:{a,keep}){for(int p:pat[q]){trials++;if(!check(q,p)){ok=false;break;}}if(!ok)break;}
   if(ok){hits++;cout<<"{\"remove\":"<<a<<",\"keep\":"<<keep<<",\"actions\":[["<<z.a.w<<','<<z.a.d<<','<<z.a.n<<"],["<<o.a.w<<','<<o.a.d<<','<<o.a.n<<"]],\"patch\":["<<patch.pq<<','<<patch.pb<<','<<patch.pa.w<<','<<patch.pa.d<<','<<patch.pa.n<<"]}"<<endl;}
  }
 }
 cerr<<"DONE pairs "<<pairs<<" proposals "<<proposals<<" tests "<<trials<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t).count()<<endl;
}
