// A bounded synthesis experiment for83/190: one merged row and one helper row.
// Candidate filters alone are not certificates; full source contracts follow.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
struct Case{int tape,target;};
int main(int argc,char**argv){
 const int K=5,N=1<<(2*K+1),BOUND=80;array<A,2>rs[4096];bool ex[4096]={};vector<int>qs;int q,b,w,n;char d;ifstream f(argv[1]);
 while(f>>q>>b>>w>>d>>n){if(q==190)continue;if(!ex[q])qs.push_back(q);ex[q]=true;rs[q][b]={w,d=='R'?1:-1,n==190?83:n};}
 set<int> forbid={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,83,94,97,113,198};
 vector<A>actions;for(int q:qs)for(int w:{0,1})for(int d:{-1,1})actions.push_back({w,d,q});
 vector<Case>cases;for(int p=0;p<N;p++)if(((p>>(K-2))&7)==3&&((p>>K)&1)==0){int marker=p>>(K-3)&1;cases.push_back({p,marker?99:93});}
 // Put small examples first, then all arbitrary exteriors in the window.
 stable_sort(cases.begin(),cases.end(),[](Case a,Case b){return __builtin_popcount(a.tape)<__builtin_popcount(b.tape);});
 auto execute=[&](Case tc,A first,int helper,int hb,A replacement)->bool{
  int q=83,h=0,t=tc.tape;
  for(int s=0;s<=BOUND;s++){
   if(s&&q==tc.target&&h==1&&t==tc.tape)return true;
   if(s==BOUND||abs(h)>K||!ex[q])return false;
   int bit=t>>(K+h)&1;A a=q==83&&!bit?first:q==helper&&bit==hb?replacement:rs[q][bit];
   t=(t&~(1<<(K+h)))|(a.w<<(K+h));h+=a.d;q=a.n;
  }return false;
 };
 long long trials=0,hits=0;auto started=chrono::steady_clock::now();
 int idx=0;
 for(A first:actions){
  bool alone=true;for(Case tc:cases)if(!execute(tc,first,-1,0,{0,1,83})){alone=false;break;}
  if(alone){hits++;cout<<"{\"without_helper\":true,\"action\":["<<first.w<<','<<first.d<<','<<first.n<<"]}"<<endl;}
  set<pair<int,int>>helpers;
  for(Case tc:cases){
   int q=83,h=0,t=tc.tape;set<tuple<int,int,int>>seen;
   for(int s=0;s<BOUND&&abs(h)<=K&&ex[q];s++){
    if(!seen.emplace(q,h,t).second)break;
    int bit=t>>(K+h)&1;if(!forbid.count(q))helpers.emplace(q,bit);
    A a=q==83&&!bit?first:rs[q][bit];t=(t&~(1<<(K+h)))|(a.w<<(K+h));h+=a.d;q=a.n;
   }
  }
  for(auto[h,hb]:helpers)for(A replacement:actions){if(replacement==rs[h][hb])continue;trials++;bool ok=true;for(Case tc:cases)if(!execute(tc,first,h,hb,replacement)){ok=false;break;}
   if(ok){hits++;cout<<"{\"merged_zero\":["<<first.w<<','<<first.d<<','<<first.n<<"],\"helper\":["<<h<<','<<hb<<"],\"helper_action\":["<<replacement.w<<','<<replacement.d<<','<<replacement.n<<"]}"<<endl;}
  }
  if(++idx%100==0)cerr<<"actions "<<idx<<" trials "<<trials<<" hits "<<hits<<endl;
 }
 cerr<<"DONE first_actions "<<actions.size()<<" trials "<<trials<<" cases "<<cases.size()<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}
