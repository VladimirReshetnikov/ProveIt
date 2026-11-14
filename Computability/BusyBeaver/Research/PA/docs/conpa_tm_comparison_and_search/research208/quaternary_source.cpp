#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct I{int op,r,z,p;};
int main(int argc,char**argv){ifstream f(argv[1]);int n,start;f>>n>>start;vector<I>ins(n);for(auto&i:ins)f>>i.op>>i.r>>i.z>>i.p;array<int,9>pw{};int base=1;for(int&i:pw){i=base;base*=4;}size_t total=size_t(n)*base;vector<uint64_t>seen((total+63)/64);vector<uint32_t>queue;queue.reserve(2000000);vector<array<uint8_t,9>>values(n);
 auto add=[&](int pc,int m){size_t v=size_t(pc)*base+m;if(!(seen[v>>6]&(uint64_t(1)<<(v&63)))){seen[v>>6]|=uint64_t(1)<<(v&63);queue.push_back(v);}};
 add(start,2);size_t cursor=0;
 while(cursor<queue.size()){
  uint32_t code=queue[cursor++];int pc=code/base,m=code%base;auto i=ins[pc];int v=(m/pw[i.r])%4;
  for(int r=0;r<9;r++)values[pc][r]|=1<<((m/pw[r])%4);
  if(i.op==0)add(i.p,v<3?m+pw[i.r]:m);
  else if(i.op==1){if(v==0)add(i.z,m);else if(v<3)add(i.p,m-pw[i.r]);else{add(i.p,m-pw[i.r]);add(i.p,m);}}
  else if(i.op==2)add(i.p,m);
  if(cursor%1000000==0)cerr<<"PROGRESS "<<cursor<<" queue "<<queue.size()<<endl;
 }
 cout<<"STATES "<<cursor<<endl;int reached=0;
 for(int pc=0;pc<n;pc++){
  auto i=ins[pc];if(!values[pc][0])cout<<"UNREACHED "<<pc<<endl;else{
   reached++;if(i.op==1){int v=values[pc][i.r];if(!(v&1)||!(v&14))cout<<"BRANCH "<<pc<<" r "<<i.r<<" values "<<v<<endl;}
  }
 }
 cout<<"REACHED "<<reached<<endl;
 if(argc>2){ofstream vout(argv[2]);for(int pc=0;pc<n;pc++){vout<<pc;for(auto v:values[pc])vout<<" "<<int(v);vout<<"\n";}}
}
