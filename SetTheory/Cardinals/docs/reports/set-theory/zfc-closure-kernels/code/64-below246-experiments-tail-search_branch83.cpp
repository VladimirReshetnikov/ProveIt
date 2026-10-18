// A small additional bounded family, using the same local-macro simulator.
// The fixed48/131 patch has a separate normal-return context obstruction;
// this file does not claim it is a universally valid replacement.
#define main original_pairs_driver_main
#include "search_pairs.cpp"
#undef main

int main(int argc,char**argv) {
  if(argc<3){std::cerr<<"table output [loose]\n";return 1;}
  LOOSE_SPARES=argc>=4&&std::string(argv[3])=="loose";
  std::ifstream f(argv[1]);Table t;std::string line;
  while(std::getline(f,line)){
    if(line.empty()||line[0]=='#')continue;
    std::stringstream s(line);int q,b,w,n;char d;
    s>>q>>b>>w>>d>>n;t[q][b]={w,d=='R'?1:-1,n};
  }
  std::vector<Case> cases={
    make('z',{0,0},0),make('i',{0,0},0),make('p',{1,0},0),
    make('z',{3,0,2},1),make('i',{3,2,0},1),make('p',{2,1,3},1),
    make('i',{2,0,3,1},2),make('z',{2,3,0,1},2),make('p',{1,2,4,3},2)};
  for(const auto&c:cases)if(simulate(t,c)<0){std::cerr<<"baseline failed\n";return 2;}
  t[75][0]={0,-1,112};t[48][0]={1,-1,131};t[131][0]={0,1,7};
  t[255][0]={};t[255][1]={};
  std::vector<uint64_t>pass(cases.size());uint64_t recipes=0;
  std::vector<Row> survivors;
  for(int w=0;w<2;w++)for(int d:{-1,1})for(int q=0;q<256;q++){
    if(t[q][0].w<0)continue;
    recipes++;t[83][0]={w,d,q};bool okay=true;
    for(int i=0;i<(int)cases.size();i++){
      if(simulate(t,cases[i])<0){okay=false;break;}
      pass[i]++;
    }
    if(okay)survivors.push_back({w,d,q});
  }
  std::ofstream out(argv[2]);
  out<<"{\"recipes\":"<<recipes<<",\"loose_spares\":"<<(LOOSE_SPARES?"true":"false")<<",\"staged_pass_counts\":[";
  for(int i=0;i<(int)pass.size();i++){if(i)out<<",";out<<pass[i];}
  out<<"],\"survivors\":[";
  for(int i=0;i<(int)survivors.size();i++){
    if(i)out<<",";auto r=survivors[i];out<<"[83,0,"<<r.w<<","<<r.d<<","<<r.q<<"]";
  }
  out<<"],\"scope\":\"Bounded local filter; not an impossibility theorem.\"}\n";
  std::cout<<"recipes "<<recipes<<" loose "<<LOOSE_SPARES<<" passes";
  for(auto n:pass)std::cout<<" "<<n;
  std::cout<<"\n";
}
