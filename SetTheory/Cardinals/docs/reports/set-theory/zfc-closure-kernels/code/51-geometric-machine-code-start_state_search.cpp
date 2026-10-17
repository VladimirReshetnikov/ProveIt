#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
struct Row {int w=0,d=1,t=254;};
int main(int argc,char**argv){
 if(argc<3)return 2;int limit=std::stoi(argv[2]);bool arbitrary=argc>3;
 Row rows[1000][2];std::vector<int>states;
 std::ifstream in(argv[1]);std::string line;
 while(std::getline(in,line)){
  if(line.empty()||line[0]=='#')continue;
  std::istringstream s(line);int q,b,w,t;char d;s>>q>>b>>w>>d>>t;
  rows[q][b]={w,d=='R'?1:-1,t};if(b==0)states.push_back(q);
 }
 int width=2*limit+2000,off=limit+1000;std::vector<unsigned char> tape(width);
 for(int start:states){
  std::fill(tape.begin(),tape.end(),0);int q=start,h=off,lo=width,hi=-1;
  bool success=false;
  for(int n=0;n<=limit;++n){
   if(q==254)break;
   if(q==96 && lo==h-1 && hi>=h){
    int hdr=h;while(hdr<=hi&&!tape[hdr])++hdr;
    if(hdr-h>=40){
     int p=hdr+1,regs=0;bool good=true;std::vector<int> values;
     while(p<=hi){
      if(tape[p]){good=false;break;}++p;
      int v=0;while(p<=hi&&tape[p]){++p;++v;}
      if(!v||(!arbitrary&&regs<9&&v!=1)){good=false;break;}++regs;values.push_back(v-1);
     }
     if(good&&regs>=9){
      std::cout<<"{\"start\":"<<start<<",\"steps\":"<<n<<",\"head\":"<<h-off<<",\"gap\":"<<hdr-h<<",\"register_blocks\":"<<regs<<",\"ones\":[";
      bool first=true;for(int k=lo;k<=hi;++k)if(tape[k]){if(!first)std::cout<<',';first=false;std::cout<<k-off;}
      std::cout<<"],\"values\":[";first=true;for(int v:values){if(!first)std::cout<<',';first=false;std::cout<<v;}std::cout<<"]}\n";success=true;break;
     }
    }
   }
   if(n==limit)break;Row r=rows[q][tape[h]];
   tape[h]=r.w;
   if(r.w){lo=std::min(lo,h);hi=std::max(hi,h);}
   else {if(h==lo){while(lo<=hi&&!tape[lo])++lo;}if(h==hi){while(hi>=lo&&!tape[hi])--hi;}}
   if(lo>hi){lo=width;hi=-1;}
   q=r.t;h+=r.d;
  }
 }
}
