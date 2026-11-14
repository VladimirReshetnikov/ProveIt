// Finite observed-context candidate screen, not a proof.
#include <algorithm>
#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <iostream>
#include <cstdint>
#include <chrono>
using namespace std;
struct Tr{int w,d,z;};Tr tab[1000][2];bool exists[1000];vector<uint64_t> ctx[1000][2];
struct Case{int q;uint64_t tape;};
uint64_t rng=64293473829ULL;uint64_t random64(){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
int dropq,keepq,limit=31,only=-1,radius=5;Tr repl[2];bool assigned[2]={false,false};vector<Tr> actions;vector<Case> cases;ofstream out;
long long branchcount=0,fullchecks=0,found=0;
int project(int q){return q==dropq?keepq:q;}
// returns 2 on match, -1 on fail, missing variable index on unknown.
int check(const Case &c){
 int b=(c.tape>>32)&1;Tr old=tab[c.q][b];int es=project(old.z),eh=32+old.d;
 uint64_t expected=(c.tape&~(1ULL<<32))|(uint64_t(old.w)<<32);
 int s=keepq,h=32;uint64_t tape=c.tape;
 for(int i=0;i<limit;i++){
  if(s==254||h<0||h>63)return -1;
  int bit=(tape>>h)&1;Tr t;
  if(s==keepq){if(!assigned[bit])return bit;t=repl[bit];}else t=tab[s][bit];
  tape=(tape&~(1ULL<<h))|(uint64_t(t.w)<<h);h+=t.d;s=project(t.z);
  if(s==es&&h==eh&&tape==expected)return 2;
 }
 return -1;
}
void solve(size_t from){
 for(size_t i=from;i<cases.size();i++){
  int res=check(cases[i]);if(res<0)return;
  if(res==2)continue;
  for(auto a:actions){repl[res]=a;assigned[res]=true;branchcount++;solve(i);}
  assigned[res]=false;return;
 }
 fullchecks++;
 if(!assigned[0]||!assigned[1]){cerr<<"unassigned winner\n";return;}
 found++;out<<dropq<<' '<<keepq;for(int b=0;b<2;b++)out<<' '<<repl[b].w<<' '<<repl[b].d<<' '<<repl[b].z;out<<'\n';out.flush();
 cout<<"FOUND "<<dropq<<"->"<<keepq;for(int b=0;b<2;b++)cout<<" | "<<repl[b].w<<' '<<repl[b].d<<' '<<repl[b].z;cout<<endl;
}
int main(int argc,char**argv){
 if(argc<4)return 1;if(argc>4)limit=stoi(argv[4]);if(argc>5)only=stoi(argv[5]);if(argc>6)radius=stoi(argv[6]);ifstream in(argv[1]);string ln;
 while(getline(in,ln)){if(ln.empty()||ln[0]=='#')continue;int q,b,w,z;char d;istringstream ss(ln);ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};exists[q]=true;}
 ifstream ct(argv[2]);int q,code;while(ct>>q>>code){uint64_t known=uint64_t(code)<<(32-radius);int b=(code>>radius)&1;ctx[q][b].push_back(known);ctx[q][b].push_back(known|(random64()&~(((1ULL<<(2*radius+1))-1)<<(32-radius))));}
 vector<int> st;for(int q=0;q<1000;q++)if(exists[q])st.push_back(q);out.open(argv[3]);long pairs=0;auto start=chrono::steady_clock::now();
 for(int dq:st){if(dq==0&&only!=0)continue;if(only>=0&&dq!=only)continue;dropq=dq;
  for(int kq:st){if(kq==dq)continue;keepq=kq;pairs++;actions.clear();cases.clear();
   for(int z:st)if(z!=dropq)for(int d:{-1,1})for(int w:{0,1})actions.push_back({w,d,z});
   for(size_t i=0;;i++){bool any=false;for(int b=0;b<2;b++)for(int oq:{dropq,keepq})if(i<ctx[oq][b].size()){cases.push_back({oq,ctx[oq][b][i]});any=true;}if(!any)break;}
   assigned[0]=assigned[1]=false;solve(0);
  }
  if(dq%10==0){auto sec=chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-start).count();cerr<<"progress "<<dq<<" pairs "<<pairs<<" branches "<<branchcount<<" found "<<found<<" seconds "<<sec<<endl;}
 }
 auto sec=chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-start).count();cout<<"DONE pairs "<<pairs<<" branches "<<branchcount<<" found "<<found<<" seconds "<<sec<<endl;
}
