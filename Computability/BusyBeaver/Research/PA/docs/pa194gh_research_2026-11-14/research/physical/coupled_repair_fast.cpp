#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};
struct W{int pc,branch,q;set<int>a,b;};
int main(int argc,char**argv){
 if(argc<6){cerr<<"table witnesses changed-state1 changed-state2 bound\n";return 2;}
 array<A,2>base[3000],row[3000];vector<int>qs;bool ex[3000]={};
 int q,b,w,n;char d;ifstream f(argv[1]);while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]={w,d=='R'?1:-1,n};}
 int q1=stoi(argv[3]),q2=stoi(argv[4]),bound=stoi(argv[5]);
 base[51][0]={0,1,16};vector<W> ws;ifstream wf(argv[2]);int pc,branch,sz;
 while(wf>>pc>>branch>>q>>sz){W x{pc,branch,q};for(int j=0;j<sz;j++){wf>>n;x.a.insert(n);}wf>>q>>sz;for(int j=0;j<sz;j++){wf>>n;x.b.insert(n);}ws.push_back(x);}
 vector<A>acts;for(int w=0;w<2;w++)for(int d:{-1,1})for(int q:qs)acts.push_back({w,d,q});
 long candidates=0,ticks=0,survive=0;vector<long>failure(ws.size());auto t0=chrono::steady_clock::now();
 for(A a:acts)for(A b:acts){candidates++;for(int q:qs)row[q]=base[q];row[q1][0]=a;row[q2][0]=b;
  bool good=true;
  for(int i=0;i<(int)ws.size();i++){
   W&x=ws[i];array<unsigned char,1024>tape{},goal{};for(int p:x.a)tape[p+512]=1;for(int p:x.b)goal[p+512]=1;int errors=0;for(int p=0;p<1024;p++)errors+=tape[p]!=goal[p];int q=x.q,h=0;bool passed=false;
   for(int st=1;st<=bound;st++){
    if(q==254||abs(h)>500)break;
    int ix=h+512;A act=row[q][tape[ix]];errors-=tape[ix]!=goal[ix];tape[ix]=act.w;errors+=tape[ix]!=goal[ix];h+=act.d;q=act.n;ticks++;
    if(q==84&&h==0&&errors==0){passed=true;break;}
   }
   if(!passed){good=false;failure[i]++;break;}
  }
  if(good){survive++;cout<<"{\"q1\":"<<q1<<",\"action1\":["<<a.w<<","<<a.d<<","<<a.n<<"],\"q2\":"<<q2<<",\"action2\":["<<b.w<<","<<b.d<<","<<b.n<<"]}"<<endl;}
 }
 cerr<<"candidates "<<candidates<<" survive "<<survive<<" ticks "<<ticks<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<" failures";for(long n:failure)cerr<<' '<<n;cerr<<'\n';
}
