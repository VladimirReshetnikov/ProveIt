// Independent step-at-a-time parent or candidate replay for finite controls.
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Row { int w,d,n; };
int main(int argc,char **argv){
 if(argc!=4)return 1;
 Row t[196][2];bool seen[196][2]={};ifstream f(argv[1]);int q,b,w,n;char d;int count=0;
 while(f>>q>>b>>w>>d>>n){
  if(q<0||q>=196||b<0||b>1||w<0||w>1||(d!='R'&&d!='L')||n<0||n>196||seen[q][b])return 2;
  seen[q][b]=true;t[q][b]={w,d=='R'?1:-1,n};count++;
 }
 if(count!=392)return 3;
 uint64_t bound=stoull(argv[2]);bool child=string(argv[3])=="child";
 vector<uint8_t> tape(4194304);constexpr int64_t bias=2097152;int64_t head=bias;q=0;
 for(uint64_t k=0;k<bound;k++){
  if(q==196||head<0||head>=int64_t(tape.size()))return 4;
  int read=tape[head];Row r=t[q][read];
  if(child&&q==184&&read==1)r={1,-1,75};
  if(child&&r.n==45)r.n=160;
  tape[head]=r.w;head+=r.d;q=r.n;
 }
 cout<<"direct "<<bound<<" q "<<q<<" h "<<head-bias<<"\n";
 bool in=false;int64_t lo=0;cout<<"ones_runs";
 for(int64_t p=0;p<int64_t(tape.size());p++){
  bool one=tape[p];if(one&&!in){lo=p;in=true;}if(!one&&in){cout<<' '<<lo-head<<':'<<p-1-head;in=false;}
 }
 if(in)cout<<' '<<lo-head<<':'<<int64_t(tape.size())-1-head;
 cout<<"\n";
 return 0;
}
