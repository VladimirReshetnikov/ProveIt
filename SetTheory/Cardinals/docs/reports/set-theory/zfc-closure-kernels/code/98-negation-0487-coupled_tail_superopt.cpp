// Search delete-255 plus a freely synthesized predecessor and one repair row.
// This is a nonseparable two-row search: neither mutation is filtered alone.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using Tape=std::array<uint64_t,16>;
struct Row{int w,d,t;};using Table=std::array<std::array<Row,2>,256>;
struct Case{int start,finish,head;Tape initial{},target{};};
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,int b){uint64_t v=uint64_t(1)<<(h&63);if(b)t[h>>6]|=v;else t[h>>6]&=~v;}
bool run(const Table&t,const Case&c,int fuel){Tape a=c.initial;int h=64,q=c.start;for(int k=0;k<fuel;k++){
 if(k&&q==c.finish&&h==c.head+64&&a==c.target)return true;
 if(h<0||h>=1024||q==255||q==254)return false;
 Row r=t[q][get(a,h)];set(a,h,r.w);h+=r.d;q=r.t;
 }return false;}
int main(int argc,char**argv){
 if(argc<2||argc>3)return 2;std::ifstream in(argv[1]);int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cs(nc);
 for(auto&c:cs){int n,x;in>>c.start>>c.finish>>c.head>>n;for(int i=0;i<n;i++){in>>x;set(c.initial,x+64,1);}in>>n;for(int i=0;i<n;i++){in>>x;set(c.target,x+64,1);}}
 // Baseline execution permits 255.
 auto baseline=[&](const Case&c){Tape a=c.initial;int h=64,q=c.start;for(int k=0;k<2000;k++){if(k&&q==c.finish&&h==c.head+64&&a==c.target)return true;if(h<0||h>=1024||q==254)return false;Row r=old[q][get(a,h)];set(a,h,r.w);h+=r.d;q=r.t;}return false;};
 for(int i=0;i<nc;i++)if(!baseline(cs[i])){std::cerr<<"BASELINE FAIL "<<i<<"\n";return 1;}
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;std::mt19937 rng(1418);std::shuffle(order.begin(),order.end(),rng);
 std::vector<int>repairs{2,4,6,7,10,14,20,42,48,63,73,75,83,95,109,112,131};
 std::vector<int>targets=repairs;
 std::string prefix="coupled-tail";
 if(argc==3){targets=states;targets.erase(std::remove(targets.begin(),targets.end(),255),targets.end());targets.push_back(254);prefix=argv[2];}
 auto began=std::chrono::steady_clock::now();uint64_t tested=0,full=0,success=0;
 std::ofstream out(prefix+"-survivors.txt");
 for(int repair:repairs)for(int bit:{0,1}){
  if(repair==75&&bit==0)continue;Table t=old;
  for(int w:{0,1})for(int d:{-1,1})for(int target:targets){
   t[75][0]={w,d,target};
   for(int w2:{0,1})for(int d2:{-1,1})for(int target2:targets){
    t[repair][bit]={w2,d2,target2};tested++;
    bool good=true;for(int i=0;i<12;i++)if(!run(t,cs[order[i]],2000)){good=false;break;}
    if(!good)continue;full++;for(int i:order)if(!run(t,cs[i],2000)){good=false;break;}
    if(good){success++;out<<w<<' '<<d<<' '<<target<<' '<<repair<<' '<<bit<<' '<<w2<<' '<<d2<<' '<<target2<<'\n';out.flush();}
   }
  }
  std::cerr<<"repair "<<repair<<"/"<<bit<<" tables "<<tested<<" full "<<full<<" survivors "<<success<<"\n";
 }
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 std::ofstream report(prefix+"-summary.json");report<<"{\"tables_tested\":"<<tested<<",\"past_probes\":"<<full<<",\"survivors\":"<<success<<",\"macro_cases\":"<<nc<<",\"fuel\":2000,\"target_states\":"<<targets.size()<<",\"seconds\":"<<sec<<",\"finite_only\":true}\n";
}
