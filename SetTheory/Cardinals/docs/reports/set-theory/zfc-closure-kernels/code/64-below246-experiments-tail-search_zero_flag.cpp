#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>
struct Row{int w=-1,d=0,q=-1;};
using Table=std::array<std::array<Row,2>,256>;
constexpr int SHIFT=5104,SIZE=10496,FUEL=5000;
bool STRICT=false;
struct Case{std::string path,op,positive;int reg,seed,head,header,end;std::array<uint8_t,SIZE> init{},want{},grown{};};
bool suffix(const std::array<uint8_t,SIZE>&tape,int start){
 int last=SIZE-1;while(last>=start&&tape[last]==0)last--;
 if(last<start)return false;
 int j=start;
 while(j<=last){if(tape[j++]!=0)return false;int n=0;while(j<=last&&tape[j]){j++;n++;}if(n==0)return false;}
 return true;
}
int sim(const Table&t,const Case& c){
 auto tape=c.init;int q=96,h=SHIFT,dispatch=0;
 for(int k=0;k<=FUEL;k++){
  if(k&&q==96){
   if(h==c.head+SHIFT){
    if(STRICT){if(tape==c.want)return k;}
    else{
     if(std::equal(tape.begin(),tape.begin()+c.end+SHIFT,c.want.begin())&&suffix(tape,c.end+SHIFT))return k;
     if(std::equal(tape.begin(),tape.begin()+c.end+SHIFT+1,c.grown.begin())&&suffix(tape,c.end+SHIFT+1))return k;
    }
   }
   if(++dispatch>15)return -1;
  }
  if(k==FUEL||h<0||h>=SIZE||q<0||q>=256)return -1;
  Row r=t[q][tape[h]];if(r.w<0)return -1;tape[h]=r.w;h+=r.d;q=r.q;
 }
 return -1;
}
int main(int argc,char**argv){
 if(argc<4)return 1;
 STRICT=argc>=5&&std::string(argv[4])=="strict";
 Table t;std::string line;std::ifstream f(argv[1]);
 while(std::getline(f,line)){if(line.empty()||line[0]=='#')continue;std::stringstream s(line);int q,b,w,n;char d;s>>q>>b>>w>>d>>n;t[q][b]={w,d=='R'?1:-1,n};}
 std::vector<Case>cases;std::ifstream cf(argv[2]);
 while(std::getline(cf,line)){Case c;std::stringstream s(line);int count,x;s>>c.path>>c.op>>c.reg>>c.seed>>c.positive>>c.head>>count;while(count--){s>>x;c.init[x+SHIFT]=1;}s>>count;while(count--){s>>x;c.want[x+SHIFT]=1;}s>>c.header>>c.end;for(int j=0;j<SIZE-1;j++)if(c.want[j])c.grown[j+(j>=SHIFT+c.header)]=1;cases.push_back(c);}
 for(int i=0;i<(int)cases.size();i++)if(sim(t,cases[i])<0){std::cerr<<"baseline failed case"<<i<<"\n";return 2;}
 t[75][0]={0,1,255};t[255][1]={1,-1,63};t[48][0]={0,-1,112};t[112][0]={1,1,10};t[131][0]={};t[131][1]={};
 std::vector<Row>choices;for(int w=0;w<2;w++)for(int d:{-1,1})for(int q=0;q<256;q++)if(q!=131&&t[q][0].w>=0)choices.push_back({w,d,q});
 std::ofstream out(argv[3]);out<<"[\n";bool first=true;
 std::ofstream partial(std::string(argv[3])+".partial.jsonl");
 uint64_t tried=0;std::vector<uint64_t>pass(cases.size());auto start=std::chrono::steady_clock::now();
 for(auto tail:choices)for(auto flag:choices){
  tried++;t[255][0]=tail;t[112][1]=flag;bool good=true;
  for(int i=0;i<(int)cases.size();i++){if(sim(t,cases[i])<0){good=false;break;}pass[i]++;if(i==1)partial<<"{\"tail\":["<<tail.w<<","<<tail.d<<","<<tail.q<<"],\"flag\":["<<flag.w<<","<<flag.d<<","<<flag.q<<"]}\n";}
  if(!good)continue;
  if(!first)out<<",\n";first=false;
  out<<"{\"tail\":["<<tail.w<<","<<tail.d<<","<<tail.q<<"],\"flag\":["<<flag.w<<","<<flag.d<<","<<flag.q<<"]}";out.flush();
  std::cout<<"SURVIVOR tail="<<tail.w<<","<<tail.d<<","<<tail.q<<" flag="<<flag.w<<","<<flag.d<<","<<flag.q<<std::endl;
 }
 out<<"\n]\n";
 std::cout<<"choices "<<choices.size()<<" recipes "<<tried<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" pass";
 for(auto n:pass)std::cout<<" "<<n;std::cout<<"\n";
}
