// Discovery domain only: observed finite frames, not an inductive invariant.
#include "frame_support.hpp"
int main(int argc,char**argv){
 if(argc<4){cerr<<"table cases output\n";return 2;}
 vector<int>states;Table T=load_table(argv[1],states);auto cases=load_cases(argv[2]);
 vector<bitset<32768>> masks(MAXQ);long total=0,boots=0;
 auto record=[&](int q,int h,const Tape&t){int m=0;for(int d=-7;d<=7;d++)m|=int(t.read(h+d))<<(d+7);masks[q].set(m);total++;};
 for(const auto&c:cases){
  Tape t=c.input;int q=84,h=0,k=0;
  for(;k<20000;k++){
   if(q==254){if(c.targetq!=254)throw runtime_error("Wrong baseline halt");break;}
   if(k&&q==c.targetq&&h==c.targeth&&t==c.target)break;
   record(q,h,t);auto a=T[2*q+t.read(h)];t.write(h,a.w);h+=a.d;q=a.z;
  }
  if(k==20000)throw runtime_error("Baseline did not finish finite interface");
 }
 Tape t;int q=0,h=0,k=0;
 for(;k<1000000;k++){
  if(q==84&&!parse_root(h,t).empty())break;
  if(q==254)throw runtime_error("Bootstrap halt");
  record(q,h,t);auto a=T[2*q+t.read(h)];t.write(h,a.w);h+=a.d;q=a.z;
 }
 if(k==1000000)throw runtime_error("Bootstrap did not finish");boots=k;
 ofstream out(argv[3]);out<<7<<' '<<states.size()<<'\n';size_t n=0;
 for(int q:states){out<<q<<' '<<masks[q].count();n+=masks[q].count();for(int m=0;m<32768;m++)if(masks[q][m])out<<' '<<m;out<<'\n';}
 cout<<"{\"scope\":\"Observed finite contexts only\",\"contexts\":"<<n<<",\"cases\":"<<cases.size()<<",\"steps\":"<<total<<",\"startup_steps\":"<<boots<<"}\n";
}
