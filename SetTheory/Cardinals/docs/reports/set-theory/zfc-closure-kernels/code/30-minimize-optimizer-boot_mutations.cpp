#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
struct Row {int w,d,q;};using Table=std::array<std::array<Row,2>,255>;
struct Mutation {int a,b,w,d,q;};
constexpr int Z=1000000;
std::vector<uint8_t> tape(2*Z);int usedlo=Z,usedhi=Z;
void simulate(const Table&T,int start,int id,int64_t fuel){
 std::fill(tape.begin()+usedlo,tape.begin()+usedhi+1,0);usedlo=usedhi=Z;
 int h=Z,q=start,lo=Z+1,hi=Z-1,ones=0;int64_t visits=0;std::map<std::vector<int>,int64_t>seen;
 std::string outcome="fuel_limit";int64_t n;int frames=0;
 for(n=0;n<fuel;n++){
  if(q==254){outcome="halt";break;}
  if(q==5||q==8){outcome="deleted_state";break;}
  if(q==96){visits++;if(lo==h-1&&tape[h-1]){
   int x=h+34;while(x<=hi&&!tape[x])x++;int header=x-h;
   if(x<=hi&&header>=40){std::vector<int>regs;x++;while(x<hi&&!tape[x]&&tape[x+1]){int begin=++x;while(x<=hi&&tape[x])x++;regs.push_back(x-begin-1);}if(x>hi&&regs.size()>=9){
    std::cout<<"{\"type\":\"frame\",\"candidate\":"<<id<<",\"start\":"<<start<<",\"steps\":"<<n<<",\"head\":"<<h-Z<<",\"header\":"<<header<<",\"pc\":\"";for(int j=0;j<34;j++)std::cout<<int(tape[h+j]);std::cout<<"\",\"physical_primary\":[";for(int j=0;j<9;j++){if(j)std::cout<<",";std::cout<<regs[j];}std::cout<<"],\"spare_blocks\":"<<regs.size()-9<<",\"spare_nonzero\":[";bool first=true;for(int j=9;j<int(regs.size());j++)if(regs[j]){if(!first)std::cout<<",";first=false;std::cout<<"["<<j-9<<","<<regs[j]<<"]";}std::cout<<"]}\n";std::cout.flush();frames++;
    if(frames==3){outcome="three_valid_frames";break;}
   }}
  }}
  int read=tape[h];Row r=T[q][read];
  bool virgin=ones==0||(r.d==1?hi<h:lo>h);
  if(!read&&r.q==q&&virgin){outcome="blank_ray_self_loop";break;}
  if(ones<30&&seen.size()<2000){std::vector<int> key={q};for(int x=lo;x<=hi;x++)if(tape[x])key.push_back(x-h);auto it=seen.find(key);if(it!=seen.end()){outcome="exact_translation_cycle";break;}seen.emplace(std::move(key),n);}
  tape[h]=r.w;ones+=r.w-read;
  if(r.w){if(ones==1)lo=hi=h;else{lo=std::min(lo,h);hi=std::max(hi,h);}}
  else if(read){if(!ones){lo=h+1;hi=h-1;}else{if(h==lo)while(lo<=hi&&!tape[lo])lo++;if(h==hi)while(hi>=lo&&!tape[hi])hi--;}}
  usedlo=std::min(usedlo,h);usedhi=std::max(usedhi,h);
  h+=r.d;q=r.q;
  if(h<10||h+500>=2*Z){outcome="finite_tape_bound";break;}
 }
 std::cout<<"{\"type\":\"result\",\"candidate\":"<<id<<",\"start\":"<<start<<",\"outcome\":\""<<outcome<<"\",\"steps\":"<<n<<",\"dispatches\":"<<visits<<",\"frames\":"<<frames<<",\"state\":"<<q<<",\"head\":"<<h-Z<<",\"ones\":"<<ones<<"}\n";
}
int main(int argc,char**argv){
 Table base;for(auto &q:base)for(auto&r:q)r={0,0,254};std::ifstream in(argv[1]);std::string line;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;std::istringstream ss(line);int q,b,w,r;char d;ss>>q>>b>>w>>d>>r;base[q][b]={w,d=='R'?1:-1,r};}
 base[3][0]={0,-1,48};
 std::ifstream muts(argv[2]);int id=0;int64_t fuel=argc>3?std::stoll(argv[3]):3000000;
 while(getline(muts,line)){
  std::istringstream ss(line);int a,b,w,q;char d;ss>>a>>b>>w>>d>>q;auto T=base;T[a][b]={w,d=='R'?1:-1,q};std::set<int> reps;int cycles=0;
  for(int st=0;st<254;st++)if(st!=5&&st!=8){int p=st;std::set<int> v;while(!v.count(p)&&p!=254){v.insert(p);Row r=T[p][0];if(r.w){reps.insert(p);break;}p=r.q;}if(v.count(p)&&!T[p][0].w)cycles++;}
  std::cout<<"{\"type\":\"classification\",\"candidate\":"<<id<<",\"mutation\":["<<a<<","<<b<<","<<w<<",\""<<d<<"\","<<q<<"],\"zero_only_cycle_starts\":"<<cycles<<",\"representatives\":[";bool first=true;for(int st:reps){if(!first)std::cout<<",";first=false;std::cout<<st;}std::cout<<"]}\n";
  for(int st:reps)simulate(T,st,id,fuel);
  id++;if(id%20==0)std::cerr<<"completed "<<id<<" candidates\n";
 }
}
