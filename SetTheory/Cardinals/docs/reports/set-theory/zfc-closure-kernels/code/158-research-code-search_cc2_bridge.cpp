#define SKIP_TWO_MAIN
#include "search_two.cpp"
int main(int argc,char**argv){
 if(argc!=4)return 2;vector<int>states;auto base=load_table(argv[1],states);auto cases=load_cases(argv[2]);read_source(argv[3]);int passes=0;
 for(int helper:states){if(helper==108)continue;auto t=base;t[2*108+1]={0,-1,helper};t[2*helper]={0,-1,122};bool good=true;long tested=0;
  for(auto&c:cases){auto r=probe(t,c);tested++;if(r.status){good=false;cout<<"Reject helper "<<helper<<" ordinal "<<c.ordinal<<" guard "<<c.positive<<" trial "<<c.trial<<" status "<<r.status<<" cases "<<tested<<'\n';break;}}
  if(good){passes++;cout<<"FINITE PASS helper "<<helper<<'\n';auto r=bootstrap_any(t,0);cout<<"BOOT status "<<r.status<<" steps "<<r.steps<<'\n';}
 }
 cerr<<"Finite survivors "<<passes<<'\n';
}
