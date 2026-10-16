#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
struct Row {int w,d,q;};
int main(int argc,char**argv){
 std::array<std::array<Row,2>,255>T;for(auto &q:T)for(auto&r:q)r={0,0,254};
 std::ifstream in(argv[1]);std::string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;std::istringstream ss(line);int q,b,w,r;char d;ss>>q>>b>>w>>d>>r;T[q][b]={w,d=='R'?1:-1,r};}
 T[3][0]={0,-1,48};T[5][0]={1,1,97};T[5][1]={1,1,64};T[49][1]={0,1,64};if(argc>3){T[49][1]={1,-1,std::stoi(argv[3])};}
 const int Z=4000000;std::vector<uint8_t> tape(2*Z);int h=Z,q=96,lo=Z-1,hi=Z+3;tape[lo]=tape[hi]=1;
 int64_t fuel=argc>2?std::stoll(argv[2]):1000000000LL, visits=0, frames=0;auto start=std::chrono::steady_clock::now();
 auto printframe=[&](int64_t n,int header,const std::vector<int>&regs){std::cout<<"{\"steps\":"<<n<<",\"head\":"<<h-Z<<",\"header\":"<<header<<",\"pc\":\"";for(int j=0;j<34;j++)std::cout<<int(tape[h+j]);std::cout<<"\",\"physical\":[";for(int j=0;j<int(regs.size());j++){if(j)std::cout<<",";std::cout<<regs[j];}std::cout<<"]}"<<std::endl;};
 for(int64_t n=0;n<=fuel;n++){
  if(q==96){visits++;if(lo==h-1&&tape[h-1]){
   int x=h+34;while(x<=hi&&!tape[x])x++;int header=x-h;
   if(x<=hi&&header>=40){std::vector<int>regs;x++;while(x<hi&&!tape[x]&&tape[x+1]){int begin=++x;while(tape[x])x++;regs.push_back(x-begin-1);}if(x>hi&&regs.size()>=9){frames++;printframe(n,header,regs);if(frames>=5)return 0;}}
  }}
  if(q==254){std::cout<<"HALT "<<n<<std::endl;return 0;}
  if(n==fuel)break;
  Row r=T[q][tape[h]];tape[h]=r.w;if(r.w){lo=std::min(lo,h);hi=std::max(hi,h);}else if(h==lo||h==hi){while(lo<hi&&!tape[lo])lo++;while(hi>lo&&!tape[hi])hi--;}
  h+=r.d;q=r.q;
  if(h<10||h+500>=2*Z){std::cout<<"BOUND "<<n<<std::endl;return 0;}
  if(n%100000000==99999999){double s=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cerr<<"steps "<<n+1<<" seconds "<<s<<" head "<<h-Z<<" span "<<hi-lo+1<<" dispatch "<<visits<<" frames "<<frames<<std::endl;}
 }
 std::cout<<"{\"outcome\":\"fuel_limit\",\"fuel\":"<<fuel<<",\"dispatch_visits\":"<<visits<<",\"valid_frames\":"<<frames<<",\"state\":"<<q<<",\"head\":"<<h-Z<<",\"ones\":[";
 bool first=true;for(int x=lo;x<=hi;x++)if(tape[x]){if(!first)std::cout<<",";first=false;std::cout<<x-Z;}std::cout<<"]}\n";
}
