// Context-specific one-step state elimination, derived from attributed fixture interpreter.
#define main inherited_pair_main
#include "pair_merge_search.cpp"
#undef main
bool execute_at(const Table&T,const Case&c,int q,int h,int fuel=20000){Tape tape=c.initial;for(int step=1;step<=fuel;step++){if(h<0||h>=2048)return false;int b=get(tape,h);auto r=T[q][b];set(tape,h,r.w);h+=r.d;q=r.t;if(q==254)return c.halt;if(!c.halt&&q==96&&h==c.head+64&&tape==c.target)return true;}return false;}
int main(int argc,char**argv){
 std::ifstream in(argc>1?argv[1]:"candidate245-literal-cases.txt");int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cs(nc);for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
 std::bitset<512>all;for(auto&c:cs){if(!execute(old,c,96,96,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}all|=c.used;}
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;std::mt19937 rng(20261018);std::shuffle(order.begin(),order.end(),rng);
 std::array<std::vector<int>,512>affected;for(int hole=0;hole<512;hole++)for(int idx:order)if(cs[idx].used[hole])affected[hole].push_back(idx);
 long long tests=0,checks=0;int holestested=0,replacements=0,passedprobe=0;std::array<std::vector<Row>,512>options;std::ofstream out("context-action-options.txt");auto began=std::chrono::steady_clock::now();
 for(int source:states)for(int bit=0;bit<2;bit++){
  int hole=source*2+bit,dead=old[source][bit].t;if(dead==source||dead==96||dead==254)continue;
  if(affected[hole].empty())throw 1;
  int probe=affected[hole][0];for(int idx:affected[hole])if(cs[idx].steps<cs[probe].steps)probe=idx;
  Case c=cs[probe];int q=96,h=64;
  for(int step=0;step<20000;step++){int b=get(c.initial,h);if(q==source&&b==bit)break;auto r=old[q][b];set(c.initial,h,r.w);h+=r.d;q=r.t;}
  if(q!=source||get(c.initial,h)!=bit)throw 2;
  holestested++;
  for(int dst:states)if(dst!=dead)for(int w=0;w<2;w++)for(int d:{-1,1}){
   Table T=old;T[source][bit]={w,d,dst};tests++;
   if(!execute_at(T,c,source,h))continue;passedprobe++;bool good=true;
   for(int idx:affected[hole]){checks++;if(idx!=probe&&!execute_at(T,cs[idx],96,64)){good=false;break;}}
   // The shortened probe gets its own full-input fuel check before acceptance.
   if(good&&!execute_at(T,cs[probe],96,64))throw 3;
   if(good){options[hole].push_back({w,d,dst});replacements++;out<<source<<" "<<bit<<" "<<dead<<" "<<w<<" "<<d<<" "<<dst<<"\n";out.flush();}
  }
  if(!options[hole].empty())std::cerr<<"ROW "<<source<<"/"<<bit<<" olddst="<<dead<<" alternatives="<<options[hole].size()<<"\n";
 }
 int possible=0,combined=0;std::ofstream sols("context-elimination-candidates.txt");
 for(int dead:states){if(dead==96||dead==95)continue;std::vector<int>incoming;bool good=true;
  for(int q:states)if(q!=dead)for(int b=0;b<2;b++)if(old[q][b].t==dead){incoming.push_back(2*q+b);if(options[2*q+b].empty())good=false;}
  if(!good||incoming.empty())continue;possible++;Table T=old;for(int hole:incoming)T[hole/2][hole%2]=options[hole][0];
  for(int idx:order){if(!execute_at(T,cs[idx],96,64)){good=false;break;}}
  std::cerr<<"ELIM "<<dead<<" entries="<<incoming.size()<<" combined="<<good<<"\n";
  if(good){combined++;sols<<dead;for(int hole:incoming){auto r=T[hole/2][hole%2];sols<<" | "<<hole/2<<" "<<hole%2<<" "<<r.w<<" "<<r.d<<" "<<r.t;}sols<<"\n";}
 }
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();std::ofstream sum("context-action-summary.json");sum<<"{\"rows\":"<<holestested<<",\"candidates\":"<<tests<<",\"passed_probe\":"<<passedprobe<<",\"additional_checks\":"<<checks<<",\"individual_replacements\":"<<replacements<<",\"possible_eliminations\":"<<possible<<",\"verified_combined\":"<<combined<<",\"cases\":"<<nc<<",\"seconds\":"<<seconds<<",\"finite_only\":true}\n";std::cerr<<"FINISHED "<<tests<<" recipes "<<replacements<<" replacements "<<possible<<" possible deletions "<<combined<<" combinedverified seconds "<<seconds<<"\n";
}
