#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <string>
#include <vector>
struct Row{int w=-1,d=0,q=-1;};
int main(int argc,char**argv){
 if(argc!=4&&argc!=5)return 2;
 std::array<std::array<Row,2>,255> table;
 std::ifstream input(argv[1]);std::string line;
 while(std::getline(input,line)){
  if(line.empty()||line[0]=='#')continue;
  int q,b,w,t;std::string d;std::istringstream ss(line);
  if(!(ss>>q>>b>>w>>d>>t)||q<0||q>=254||b<0||b>1||w<0||w>1||t<0||t>254||(d!="L"&&d!="R")||table[q][b].w!=-1)return 3;
  table[q][b]={w,d=="R"?1:-1,t};
 }
 int q=64;int64_t h=0,offset=65536,minimum=0,maximum=-1;
 std::vector<uint8_t> tape(131072,0);uint64_t ones=0,tick=0,cap=std::stoull(argv[2]);
 auto cell=[&](int64_t pos)->uint8_t&{
  while(pos+offset<0||pos+offset>=int64_t(tape.size())){
   size_t size=tape.size();std::vector<uint8_t> grown(size*2,0);
   std::copy(tape.begin(),tape.end(),grown.begin()+size/2);offset+=size/2;tape.swap(grown);
  }
  return tape[pos+offset];
 };
 std::ofstream out(argv[3]);uint64_t visits=0,noMarker=0,badLeft=0,nonRoot=0,badFile=0;
 bool found=false;std::vector<int64_t> values;int64_t header=0;
 uint64_t rootCount=0,skip=argc==5?std::stoull(argv[4]):0;
 out<<"{\"first_dispatch_samples\":[";
 while(tick<cap&&q!=254){
  if(q==96){
   ++visits;
   if(visits<=20){
    if(visits>1)out<<',';
    out<<"{\"step\":"<<tick<<",\"actual_head\":"<<h<<",\"one_count\":"<<ones
       <<",\"minimum_one\":"<<minimum<<",\"marker_present\":"<<(int)cell(h-1)<<",\"nearby_ones\":[";
    bool comma=false;for(int64_t p=h-12;p<=h+48;++p)if(cell(p)){if(comma)out<<',';out<<p;comma=true;}out<<"]}";
   }
   if(!cell(h-1)){++noMarker;}
   else if(minimum!=h-1){++badLeft;}
   else{
    header=h;while(header<=maximum&&!cell(header))++header;
    if(header>maximum||header-h<3){++nonRoot;}
    else{
     int64_t cursor=header+1;values.clear();bool good=true;
     while(cursor<=maximum){
      if(cell(cursor)){good=false;break;}++cursor;int64_t value=0;
      while(cursor<=maximum&&cell(cursor)){++value;++cursor;}
      if(value==0){good=false;break;}values.push_back(value-1);
     }
     if(!good||values.size()<9){++badFile;}
     else{++rootCount;if(rootCount>skip){found=true;break;}}
    }
   }
  }
  Row r=table[q][cell(h)];if(r.w<0)return 4;
  int old=cell(h);
  if(old!=r.w){
   if(r.w){if(!ones){minimum=maximum=h;}else{minimum=std::min(minimum,h);maximum=std::max(maximum,h);}++ones;}
   else{--ones;cell(h)=0;if(ones){if(h==minimum)while(!cell(minimum))++minimum;if(h==maximum)while(!cell(maximum))--maximum;}}
  }
  cell(h)=r.w;h+=r.d;q=r.q;++tick;
 }
 out<<"],\"status\":\""<<(found?"literal_root_frame":q==254?"halt":"fuel_cutoff")
    <<"\",\"steps\":"<<tick<<",\"state\":"<<q<<",\"head\":"<<h<<",\"one_count\":"<<ones
    <<",\"dispatch_visits\":"<<visits<<",\"missing_marker\":"<<noMarker<<",\"extra_left_ones\":"<<badLeft
    <<",\"non_root_bits_or_missing_header\":"<<nonRoot<<",\"malformed_file\":"<<badFile
    <<",\"root_frames_seen\":"<<rootCount<<",\"root_frames_skipped\":"<<skip;
 if(found){
  out<<",\"header\":"<<header<<",\"gap\":"<<header-h<<",\"values\":[";
  for(size_t i=0;i<values.size();++i){if(i)out<<',';out<<values[i];}
  out<<"],\"whole_ones\":[";bool comma=false;
  for(int64_t p=minimum;p<=maximum;++p){if(cell(p)){if(comma)out<<',';out<<p;comma=true;}}
  out<<']';
 }
 out<<"}\n";
}
