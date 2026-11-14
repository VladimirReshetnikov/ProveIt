// Bounded local quotient synthesis. Discovery only: independently replay hits.
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <vector>
#include <string>
#include <tuple>
#include <chrono>
using namespace std;
struct Row {int w,d,z; bool operator==(const Row&o)const{return w==o.w&&d==o.d&&z==o.z;}};
struct St {int label;bool fixed;array<Row,2> r;array<vector<array<int,16>>,2> c;};
vector<St> M; int NN,W,RR,LIM=71,K;
int rho(int q,int a,int z){return q==z?a:q;}
bool trial(int a,int z,const array<Row,2>&news,int q,int b){
 auto target=M[q].r[b];target.z=rho(target.z,a,z);
 const auto &contexts=M[q].c[b];
 if(contexts.empty())return false;
 for(const auto&init:contexts){
  auto tape=init;auto wanted=init;wanted[W]=target.w;
  int h=W,state=a;
  for(int k=0;k<LIM;k++){
   if(h<0||h>=K||state>=NN)return false;
   int bit=tape[h];if(bit<0)return false;
   Row r=state==a?news[bit]:M[state].r[bit];
   tape[h]=r.w;h+=r.d;state=rho(r.z,a,z);
   if(state==target.z&&h==W+target.d&&tape==wanted)goto good;
  }
  return false;
  good:;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc<3){cerr<<"usage recursive_fold contexts output [extended]\n";return 1;}
 ifstream in(argv[1]);in>>NN>>W>>RR;K=W+RR;M.resize(NN);if(K>16)return 2;
 for(int q=0;q<NN;q++){
  int fixed;in>>M[q].label>>fixed;M[q].fixed=fixed;
  for(int b=0;b<2;b++){
   int cnt;auto&r=M[q].r[b];in>>r.w>>r.d>>r.z>>cnt;
   M[q].c[b].resize(cnt);
   for(auto&c:M[q].c[b]){c.fill(-2);for(int j=0;j<K;j++)in>>c[j];}
  }
 }
 bool ext=argc>3;
 ofstream out(argv[2]);long long count=0;int hits=0;
 auto start=chrono::steady_clock::now();
 for(int a=0;a<NN;a++){
  if(M[a].fixed)continue;
  if(a%20==0)cerr<<"progress "<<a<<" candidates "<<count<<" hits "<<hits<<"\n";
  for(int z=a+1;z<NN;z++){
   if(M[z].fixed)continue;
   // Protected box rows must not change their literal successors.
   bool blocked=false;
   for(int f=0;f<NN;f++)if(M[f].fixed)for(int b=0;b<2;b++)if(M[f].r[b].z==z)blocked=true;
   if(blocked)continue;
   array<Row,2> news;
   for(int d0=0;d0<NN;d0++)for(int d1=0;d1<NN;d1++){
    if(d0==z||d1==z)continue;
    news[0]={0,-1,d0};news[1]={1,-1,d1};count++;
    if(!trial(a,z,news,a,0)||!trial(a,z,news,z,0)||!trial(a,z,news,a,1)||!trial(a,z,news,z,1))continue;
    hits++;out<<M[a].label<<' '<<M[z].label;
    for(auto&r:news)out<<' '<<r.w<<' '<<r.d<<' '<<M[r.z].label;
    out<<'\n';out.flush();
    cerr<<"HIT "<<M[a].label<<' '<<M[z].label<<" helpers "<<M[d0].label<<' '<<M[d1].label<<'\n';
   }

  }
 }
 cerr<<"done candidates "<<count<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
}
