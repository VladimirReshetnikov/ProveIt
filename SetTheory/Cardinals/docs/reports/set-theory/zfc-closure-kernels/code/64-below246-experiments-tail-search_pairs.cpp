#include <array>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>

struct Row { int w=-1,d=0,q=-1; };
using Table=std::array<std::array<Row,2>,256>;
struct Case {
  char mode;
  std::vector<int> values;
  int selected;
  std::vector<int> left;
  std::vector<uint8_t> initial,target;
  int mainlen=0;
};
constexpr int ORIGIN=8, SIZE=2304, FUEL=2000;
bool LOOSE_SPARES=false;

std::vector<uint8_t> blocks(const std::vector<int>& a, int marked=-1) {
  std::vector<uint8_t> x;
  for(int r=0;r<(int)a.size();r++) {
    x.push_back(0);
    for(int k=0;k<=a[r];k++)x.push_back(k==0&&r==marked ? 0:1);
  }
  return x;
}
void paint(std::vector<uint8_t>& tape,const std::vector<uint8_t>& x,const std::vector<int>& left,int shift=0) {
  for(int i=0;i<(int)x.size();i++)tape[ORIGIN+shift+i]=x[i];
  for(int i=0;i<(int)left.size();i++)tape[ORIGIN+shift-1-i]=left[i];
}
Case make(char mode,std::vector<int> vals,int r,std::vector<int> left={1,0,1}) {
  Case c{mode,vals,r,left,std::vector<uint8_t>(SIZE),std::vector<uint8_t>(SIZE)};
  paint(c.initial,blocks(vals,r),left);
  if(mode=='i')vals[r]++;else if(mode=='p')vals[r]--;
  auto main=blocks(vals);c.mainlen=(int)main.size();
  if(LOOSE_SPARES&&mode=='i')c.mainlen-=vals.back()+2;
  if(mode=='p'){left.insert(left.begin(),1);paint(c.target,main,left,1);}
  else paint(c.target,main,left);
  return c;
}

int simulate(const Table& t,const Case& c,std::vector<int>* extra=nullptr) {
  std::array<uint8_t,SIZE> tape;
  std::copy(c.initial.begin(),c.initial.end(),tape.begin());
  int q=c.mode=='i'?73:95, h=ORIGIN;
  for(int s=0;s<=FUEL;s++) {
    if(c.mode=='i'&&q==48&&h==ORIGIN-1) {
      if(!std::equal(tape.begin(),tape.begin()+ORIGIN+c.mainlen,c.target.begin()))return -1;
      int end=SIZE-1;while(end>=ORIGIN+c.mainlen&&tape[end]==0)--end;
      std::vector<int> out;
      int j=ORIGIN+c.mainlen;
      while(j<=end) {
        if(tape[j++]!=0)return -1;
        int k=0;while(j<=end&&tape[j]){k++;j++;}
        if(k==0)return -1;
        out.push_back(k-1);
      }
      if(LOOSE_SPARES&&out.empty())return -1;
      if(extra)*extra=out;
      return s;
    }
    if(c.mode!='i'&&q==(c.mode=='z'?112:48)&&h==(c.mode=='z'?ORIGIN-1:ORIGIN)) {
      if(std::equal(tape.begin(),tape.end(),c.target.begin()))return s;
    }
    if(s==FUEL||h<ORIGIN-1||h>=SIZE||q<0||q>=256)return -1;
    Row row=t[q][tape[h]];if(row.w<0)return -1;
    tape[h]=row.w;q=row.q;h+=row.d;
  }
  return -1;
}

int main(int argc,char**argv) {
  if(argc<4){std::cerr<<"table mode output\n";return 1;}
  LOOSE_SPARES=argc>=5&&std::string(argv[4])=="loose";
  std::ifstream f(argv[1]);Table t;std::string line;std::vector<int>qs;
  while(std::getline(f,line)){if(line.empty()||line[0]=='#')continue;
    std::stringstream s(line);int q,b,w,n;char d;s>>q>>b>>w>>d>>n;t[q][b]={w,d=='R'?1:-1,n};}
  for(int q=0;q<255;q++)if(t[q][0].w>=0)qs.push_back(q);
  std::vector<Row> choices;for(int w=0;w<2;w++)for(int d:{-1,1})for(int q:qs)choices.push_back({w,d,q});
  std::vector<Case> cases={
    make('z',{0,0},0),make('i',{0,0},0),make('p',{1,0},0),
    make('z',{3,0,2},1),make('i',{3,2,0},1),make('p',{2,1,3},1),
    make('i',{2,0,3,1},2),make('z',{2,3,0,1},2),make('p',{1,2,4,3},2),
    make('z',{0,0,0,0,0},3),make('p',{0,0,1,0,0},2),make('i',{0,0,0,0,0},3),
    make('z',{7,0,8},1,{0,1,0}),make('p',{7,9,8},1,{0,1,0}),make('i',{7,9,8},1,{0,1,0})};
  for(const auto&c:cases)if(simulate(t,c)<0){std::cerr<<"baseline failed\n";return 2;}
  std::string mode=argv[2];int aq=109,ab=0,bq=75,bb=0;
  if(mode=="75both"){aq=75;ab=1;}else if(mode!="10975"&&mode!="triple"&&mode!="inc83"){std::cerr<<"bad mode\n";return 3;}
  std::ofstream out(argv[3]);out<<"[\n";bool first=true;
  std::vector<uint64_t> survived(cases.size());uint64_t tried=0;
  auto began=std::chrono::steady_clock::now();
  auto check=[&](Row a,Row b,Row c,bool triple,Row e=Row{},bool quad=false){
    Table u=t;u[aq][ab]=a;u[bq][bb]=b;if(triple)u[75][1]=c;if(quad)u[83][0]=e;u[255][0]={};u[255][1]={};tried++;
    bool good=true;
    for(int i=0;i<(int)cases.size();i++){
      if(simulate(u,cases[i])<0){good=false;break;}survived[i]++;
    }
    if(!good)return;
    if(!first)out<<",\n";first=false;
    out<<"{\"edits\":[["<<aq<<","<<ab<<","<<a.w<<","<<a.d<<","<<a.q<<"],["<<bq<<","<<bb<<","<<b.w<<","<<b.d<<","<<b.q<<"]";
    if(triple)out<<",[75,1,"<<c.w<<","<<c.d<<","<<c.q<<"]";
    if(quad)out<<",[83,0,"<<e.w<<","<<e.d<<","<<e.q<<"]";
    out<<"],\"cases\":[";
    for(int i=0;i<(int)cases.size();i++){
      if(i)out<<",";std::vector<int>extra;int cost=simulate(u,cases[i],&extra);
      out<<"{\"steps\":"<<cost<<",\"extras\":[";
      for(int j=0;j<(int)extra.size();j++){if(j)out<<",";out<<extra[j];}out<<"]}";
    }out<<"]}";out.flush();
    std::cout<<"survivor "<<aq<<"/"<<ab<<"="<<a.w<<","<<a.d<<","<<a.q<<" 75/0="<<b.w<<","<<b.d<<","<<b.q;
    if(triple)std::cout<<" 75/1="<<c.w<<","<<c.d<<","<<c.q;std::cout<<"\n";
    if(quad)std::cout<<" 83/0="<<e.w<<","<<e.d<<","<<e.q<<"\n";
  };
  if(mode=="inc83"){
    uint64_t coretried=0,firstzero=0,decrementok=0;
    for(int w=0;w<2;w++)for(int d:{-1,1})for(auto c:choices)for(auto b:choices){
      coretried++;Row a{w,d,75};Table u=t;u[109][0]=a;u[75][0]=b;u[75][1]=c;u[255][0]={};u[255][1]={};
      if(simulate(u,cases[0])<0)continue;firstzero++;
      bool good=true;for(const auto& cs:cases)if(cs.mode!='i'&&simulate(u,cs)<0){good=false;break;}
      if(!good)continue;decrementok++;
      std::cout<<"decrement core 109/0="<<a.w<<","<<a.d<<","<<a.q<<" 75/0="<<b.w<<","<<b.d<<","<<b.q<<" 75/1="<<c.w<<","<<c.d<<","<<c.q<<std::endl;
      for(auto e:choices)check(a,b,c,true,e,true);
    }
    std::cout<<"coretried "<<coretried<<" firstzero "<<firstzero<<" decrementok "<<decrementok<<std::endl;
  }else if(mode=="triple"){
    for(int w=0;w<2;w++)for(int d:{-1,1})for(auto c:choices)for(auto b:choices)check({w,d,75},b,c,true);
  }else{
    for(auto a:choices)for(auto b:choices)check(a,b,{},false);
  }
  out<<"\n]\n";
  double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::cout<<"mode "<<mode<<" loose "<<LOOSE_SPARES<<" tried "<<tried<<" seconds "<<sec<<" staged";
  for(auto x:survived)std::cout<<" "<<x;std::cout<<"\n";
  return 0;
}
