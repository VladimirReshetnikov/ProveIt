#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n; bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
struct C{int q,h,t;};
struct Case{int oldq,bit,t;C expected;};
int main(int argc,char**argv){
 if(argc<3){cerr<<"usage table output.json [bound]\n";return 2;}
 int B=argc>3?stoi(argv[3]):31, K=argc>4?stoi(argv[4]):3; int WIDTH=2*K+1, MASK=(1<<WIDTH)-1;map<int,array<A,2>> rs;ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n)rs[q][b]={w,d=='R'?1:-1,n};
 vector<int> qs;for(auto &[q,r]:rs)qs.push_back(q);map<int,set<pair<int,int>>> entry;
 for(auto &[q,r]:rs)for(auto a:r)entry[a.n].insert({-a.d,a.w});
 map<int,vector<int>> seen;for(int q:qs)seen[q]=vector<int>(MASK+1,0);
 queue<pair<int,int>> todo;for(int t=0;t<=MASK;t++){seen[74][t]=1;todo.push({74,t});}
 long long contexts=0;
 while(!todo.empty()){
  auto [q,t]=todo.front();todo.pop();contexts++;
  A a=rs[q][(t>>K)&1];if(!rs.count(a.n))continue;
  int wt=(t&~(1<<K))|(a.w<<K);
  int nt=a.d==1 ? wt>>1 : (wt<<1)&MASK;
  int edge=a.d==1?1<<(WIDTH-1):1;
  for(int v:{nt,nt|edge})if(!seen[a.n][v]){seen[a.n][v]=1;todo.push({a.n,v});}
 }
 vector<vector<int>> patterns(qs.size());
 for(int i=0;i<(int)qs.size();i++)for(int t=0;t<=MASK;t++)if(seen[qs[i]][t])patterns[i].push_back(t);
 cerr<<"abstract contexts="<<contexts<<" total="<<qs.size()*(MASK+1)<<endl;
 ofstream ctx(string(argv[2])+".contexts.json");ctx<<"{\"radius\":"<<K<<",\"states\":{";bool firstctx=true;
 for(int i=0;i<(int)qs.size();i++){if(!firstctx)ctx<<',';firstctx=false;ctx<<'"'<<qs[i]<<"\":[";bool first=true;for(int t:patterns[i]){if(!first)ctx<<',';first=false;ctx<<t;}ctx<<']';}ctx<<"}}\n";
 long long pairs=0,acts=0,tests=0;int hits=0;ofstream out(argv[2]);out<<"[\n";
 for(int i=0;i<(int)qs.size();i++)for(int j=i+1;j<(int)qs.size();j++){
  int a=qs[i],c=qs[j];if(a==74||c==74||patterns[i].empty()||patterns[j].empty())continue;pairs++;
  auto alias=[&](int q){return q==a?c:q;};vector<A> opts[2];
  for(int bit=0;bit<2;bit++){
   vector<Case>cs;
   for(auto [ix,oq]:vector<pair<int,int>>{{i,a},{j,c}})for(int t:patterns[ix])if(((t>>K)&1)==bit){
    A x=rs[oq][bit];int e=(t&~(1<<K))|(x.w<<K);cs.push_back({oq,bit,t,{alias(x.n),x.d,e}});
   }
   for(int nq:qs){if(nq==a)continue;for(int wr=0;wr<2;wr++)for(int dr:{-1,1}){
    A action{wr,dr,nq};acts++;bool good=true;
    for(auto ca:cs){tests++;C x{c,0,ca.t};bool done=false;
     for(int st=0;st<B;st++){
      if(x.h<-K||x.h>K||!rs.count(x.q))break;int read=(x.t>>(K+x.h))&1;
      if(x.q==c&&read!=bit)break;
      A y=x.q==c?action:rs[x.q][read];
      x.t=(x.t&~(1<<(K+x.h)))|(y.w<<(K+x.h));x.h+=y.d;x.q=alias(y.n);
      if(x.q==ca.expected.q&&x.h==ca.expected.h&&x.t==ca.expected.t){done=true;break;}
     }
     if(!done){good=false;break;}
    }
    if(good)opts[bit].push_back(action);
   }}
   if(opts[bit].empty())break;
  }
  if(!opts[0].empty()&&!opts[1].empty()){
   if(hits++)out<<",\n";out<<"{\"remove\":"<<a<<",\"keep\":"<<c<<",\"actions\":[";
   for(int bit=0;bit<2;bit++){if(bit)out<<',';out<<'[';bool first=true;for(auto x:opts[bit]){if(!first)out<<',';first=false;out<<'['<<x.w<<','<<x.d<<','<<x.n<<']';}out<<']';}out<<"]}";out.flush();
   cout<<"HIT "<<a<<' '<<c<<' '<<opts[0].size()<<' '<<opts[1].size()<<endl;
  }
 }
 out<<"\n]\n";cerr<<"pairs="<<pairs<<" actions="<<acts<<" tests="<<tests<<" hits="<<hits<<" bound="<<B<<" radius="<<K<<'\n';
}
