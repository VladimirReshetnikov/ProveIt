#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
struct Row {int w=-1,d=0,q=-1;};
int main(int argc,char**argv){
 if(argc!=4)return 2;
 std::array<std::array<Row,2>,255> table;
 std::ifstream input(argv[1]); std::string line;
 while(std::getline(input,line)){
  if(line.empty()||line[0]=='#')continue;
  int q,b,w,t;std::string d;std::istringstream ss(line);
  if(!(ss>>q>>b>>w>>d>>t)||q<0||q>=254||b<0||b>1||w<0||w>1||t<0||t>254||(d!="L"&&d!="R")||table[q][b].w!=-1)return 3;
  table[q][b]={w,d=="R"?1:-1,t};
 }
 int q=64;int64_t h=0,offset=65536;std::vector<uint8_t> tape(131072,0);
 uint64_t count=0,cap=std::stoull(argv[2]); std::ofstream out(argv[3]);
 auto cell=[&](int64_t pos)->uint8_t&{
  while(pos+offset<0||pos+offset>=int64_t(tape.size())){
   size_t old=tape.size();std::vector<uint8_t> grown(old*2,0);
   std::copy(tape.begin(),tape.end(),grown.begin()+old/2);
   offset+=old/2;tape.swap(grown);
  }
  return tape[pos+offset];
 };
 uint64_t first=UINT64_MAX,hits=0;const uint64_t points[]={0,1,10,100,1000,3507,10000,82552,100000,1000000,10000000,50000000,100000000};
 auto snapshot=[&](bool full){
  out<<"{\"step\":"<<count<<",\"state\":"<<q<<",\"head\":"<<h;
  uint64_t ones=0,hash=1469598103934665603ULL;
  for(size_t i=0;i<tape.size();++i)if(tape[i]){++ones;int64_t pos=int64_t(i)-offset;uint64_t value=uint64_t(pos);for(int j=0;j<8;++j){hash^=(value>>(8*j))&255;hash*=1099511628211ULL;}}
  out<<",\"one_count\":"<<ones<<",\"ones_fnv64\":"<<hash;
  if(full&&ones<=100000){out<<",\"whole_ones\":[";bool comma=false;for(size_t i=0;i<tape.size();++i)if(tape[i]){if(comma)out<<',';out<<int64_t(i)-offset;comma=true;}out<<']';}
  out<<"}";
 };
 out<<"{\"checkpoints\":[";bool comma=false;
 while(count<cap&&q!=254){
  if(std::find(std::begin(points),std::end(points),count)!=std::end(points)){
   if(comma)out<<',';snapshot(count==1000000);comma=true;
  }
  int b=cell(h);Row r=table[q][b];if(r.w<0)return 4;
  if(q==172&&b==1){if(first==UINT64_MAX)first=count;++hits;}
  cell(h)=r.w;h+=r.d;q=r.q;++count;
 }
 out<<"],\"final\":";snapshot(true);
 out<<",\"status\":\""<<(q==254?"halt":"fuel_cutoff")<<"\",\"first_changed_row_step\":"<<first<<",\"changed_row_hits\":"<<hits<<"}\n";
 return 0;
}
