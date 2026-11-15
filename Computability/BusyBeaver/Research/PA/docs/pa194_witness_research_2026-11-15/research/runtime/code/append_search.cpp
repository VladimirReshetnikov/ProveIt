#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};struct Test{vector<int>in;array<vector<int>,9>out;};
int main(int argc,char**argv){if(argc<3)return 2;map<int,array<A,2>>rows;vector<int>states;ifstream in(argv[1]);int q,b,w,n;char d;while(in>>q>>b>>w>>d>>n){if(!rows.count(q))states.push_back(q);rows[q][b]={w,d=='R'?1:-1,n};}
 ifstream fi(argv[2]);int ct;fi>>ct;vector<Test>tests(ct);for(auto&t:tests){int n;fi>>n;for(int i=0,x;i<n;i++){fi>>x;t.in.push_back(x);}for(auto&ls:t.out){fi>>n;for(int i=0,x;i<n;i++){fi>>x;ls.push_back(x);}}}
 long long totalsteps=0;auto run=[&](const Test&t)->int{
  array<bool,4096> tape{};for(int p:t.in)tape[p+512]=true;int q=84,h=0;
  for(int step=0;step<50000;step++){
   if(step&&q==84&&h==0){vector<int>one;for(int p=0;p<4096;p++)if(tape[p])one.push_back(p-512);for(int k=0;k<9;k++)if(t.out[k]==one)return k;}
   if(h<-512||h>=3584||!rows.count(q))return -1;
   auto a=rows[q][tape[h+512]];tape[h+512]=a.w;h+=a.d;q=a.n;totalsteps++;
  }return -1;
 };
 assert(run(tests[0])==1);
 vector<int>box={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};long long trials=0,screened=0,hits=0;
 for(int q:box)for(int b:{0,1}){auto old=rows[q][b];for(int tar:states)for(int w:{0,1})for(int d:{-1,1}){
  trials++;rows[q][b]={w,d,tar};int k=run(tests[0]);if(k<2)continue;screened++;bool ok=true;
  for(int i=1;i<ct;i++){int z=run(tests[i]);if(i<9?z!=k:z<0){ok=false;break;}}
  if(ok){hits++;cout<<"{\"row\":["<<q<<','<<b<<"],\"action\":["<<w<<','<<d<<','<<tar<<"],\"append\":"<<k<<"}"<<endl;}
 }rows[q][b]=old;cerr<<"ROW "<<q<<' '<<b<<" trials "<<trials<<" screened "<<screened<<" hits "<<hits<<" steps "<<totalsteps<<endl;}
 cerr<<"DONE trials "<<trials<<" screened "<<screened<<" hits "<<hits<<" steps "<<totalsteps<<endl;
}
