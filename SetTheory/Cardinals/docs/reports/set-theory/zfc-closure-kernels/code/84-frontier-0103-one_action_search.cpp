#define main inherited_pair_main
#include "pair_merge_search.cpp"
#undef main

int main(int argc,char**argv){
  std::ifstream in(argc>1?argv[1]:"offset-zero-cases.txt");int nr;in>>nr;
  Table old{};std::vector<int> states;
  for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
  int nc;in>>nc;std::vector<Case> cs(nc);
  for(auto &c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
  std::bitset<512> all;int maximum=0;
  for(auto &c:cs){if(!execute(old,c,96,96,20000,true)){std::cerr<<"BASELINE FAILED\n";return 1;}all|=c.used;maximum=std::max(maximum,c.steps);}
  std::vector<int> order(nc);for(int i=0;i<nc;i++)order[i]=i;
  std::mt19937 rng(20261018);std::shuffle(order.begin(),order.end(),rng);
  int tested=0,survivors=0,dead_count=0;long long checks=0;
  std::ofstream out("one-action-survivors.txt");
  auto began=std::chrono::steady_clock::now();
  for(int dead:states){
    if(dead==96)continue;
    std::vector<int> incoming;
    for(int q:states)if(q!=dead)for(int b=0;b<2;b++)if(old[q][b].t==dead)incoming.push_back(q*2+b);
    if(incoming.size()!=1)continue;
    dead_count++;int hole=incoming[0],q=hole/2,b=hole%2;
    std::vector<int> affected;
    for(int idx:order)if(cs[idx].used[hole])affected.push_back(idx);
    for(int dst:states)if(dst!=dead)for(int w=0;w<2;w++)for(int d:{-1,1}){
      Table t=old;t[q][b]={w,d,dst};bool good=true;tested++;
      for(int idx:affected){checks++;if(!execute(t,cs[idx],96,96,20000)){good=false;break;}}
      if(good){survivors++;out<<dead<<" "<<q<<" "<<b<<" "<<w<<" "<<d<<" "<<dst<<"\n";out.flush();std::cerr<<"SURVIVOR "<<dead<<" via "<<q<<"/"<<b<<" -> "<<w<<" "<<d<<" "<<dst<<"\n";}
    }
  }
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
  std::ofstream summary("one-action-summary.json");
  summary<<"{\"completed\":true,\"deleted_states\":"<<dead_count<<",\"candidates\":"<<tested<<",\"checks\":"<<checks<<",\"survivors\":"<<survivors<<",\"cases\":"<<nc<<",\"baseline_maxsteps\":"<<maximum<<",\"fuel\":20000,\"seconds\":"<<seconds<<",\"finite_only\":true}\n";
  std::cerr<<"FINISHED states "<<dead_count<<" candidates "<<tested<<" checks "<<checks<<" survivors "<<survivors<<" seconds "<<seconds<<"\n";
}
