// Coupled synthesis of quotient rows and one additional compensating row.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};struct T{int old,p;};
int main(int argc,char**argv){
 if(argc<8)return 2;
 int K=stoi(argv[2]),BOUND=stoi(argv[3]),rem=stoi(argv[5]),keep=stoi(argv[6]),extra=stoi(argv[7]),eb=argc>8?stoi(argv[8]):0;
 int N=1<<(2*K+1),MASK=N-1;map<int,array<A,2>>rows;vector<int>states;ifstream fi(argv[1]);int q,b,w,n;char d;while(fi>>q>>b>>w>>d>>n){if(!rows.count(q))states.push_back(q);rows[q][b]={w,d=='R'?1:-1,n};}
 map<int,set<int>> pats;queue<pair<int,int>>todo;auto add=[&](int q,int p){if(rows.count(q)&&pats[q].insert(p).second)todo.emplace(q,p);};add(74,0);while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);if(a.d==1){add(a.n,p>>1);add(a.n,(p>>1)|(1<<(2*K)));}else{add(a.n,(p<<1)&MASK);add(a.n,((p<<1)&MASK)|1);}}
 ifstream ps(argv[4]);map<int,set<int>> custom;int p;while(ps>>q>>p)custom[q].insert(p);for(auto&[q,x]:custom)pats[q]=x;
 vector<T>tests[3];for(int q:{rem,keep})for(int p:pats[q])tests[p>>K&1].push_back({q,p});for(int p:pats[extra])if((p>>K&1)==eb)tests[2].push_back({extra,p});
 array<A,3>acts;int known=0;long long checks=0;
 auto check=[&](T tc)->int{
   checks++;A old=rows[tc.old][tc.p>>K&1];int tq=old.n==rem?keep:old.n,th=old.d,tt=(tc.p&~(1<<K))|(old.w<<K);
   int q=tc.old==rem?keep:tc.old,h=0,t=tc.p;
   for(int s=0;s<=BOUND;s++){
     if(s&&q==tq&&h==th&&t==tt)return 1;
     if(s==BOUND||h<-K||h>K||!rows.count(q))return 0;
     int b=t>>(h+K)&1;int idx=q==keep?b:((q==extra&&b==eb)?2:-1);A a;
     if(idx>=0){if(!(known>>idx&1))return 2;a=acts[idx];}else a=rows[q][b];
     t=(t&~(1<<(h+K)))|(a.w<<(h+K));h+=a.d;q=a.n==rem?keep:a.n;
   }return 0;
 };
 vector<A>choices[3];for(int v=0;v<3;v++){
   known=1<<v;
   for(int tar:states)if(tar!=rem)for(int w:{0,1})for(int d:{-1,1}){
     acts[v]={w,d,tar};bool ok=true;for(T t:tests[v])if(!check(t)){ok=false;break;}if(ok)choices[v].push_back(acts[v]);
   }
   cerr<<"VARIABLE "<<v<<" choices "<<choices[v].size()<<" tests "<<tests[v].size()<<endl;
 }
 long long combos=0,hits=0;
 known=7;for(A a:choices[0])for(A b:choices[1])for(A c:choices[2]){
   combos++;acts={a,b,c};bool ok=true;for(int j=0;j<3;j++){for(T t:tests[j])if(check(t)!=1){ok=false;break;}if(!ok)break;}
   if(ok){hits++;cout<<"{\"remove\":"<<rem<<",\"keep\":"<<keep<<",\"extra\":["<<extra<<','<<eb<<"],\"actions\":[";for(int j=0;j<3;j++){if(j)cout<<',';auto a=acts[j];cout<<'['<<a.w<<','<<a.d<<','<<a.n<<']';}cout<<"]}"<<endl;}
 }
 cerr<<"DONE combos "<<combos<<" checks "<<checks<<" hits "<<hits<<endl;
}
