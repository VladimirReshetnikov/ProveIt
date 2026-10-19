// Finite exploratory derivative of attributed resource_merge_search.cpp.
#define main inherited_pair_main
#include "pair_merge_search.cpp"
#undef main
struct Goal { std::array<int,9>regs{};std::array<bool,51>pc{};};
Goal goal(const Case&c){Goal g;if(c.halt)return g;int h=64+c.head;for(int i=0;i<51;i++)g.pc[i]=get(c.target,h+i);int pos=245;while(!get(c.target,pos))pos++;
 pos++;for(int i=0;i<9;i++){if(get(c.target,pos))throw 1;int start=++pos;while(get(c.target,pos))pos++;g.regs[i]=pos-start-1;if(g.regs[i]<0)throw 2;}return g;}
bool frame(const Tape&a,int h,const Goal&g){
 if(h<1||h>1800||!get(a,h-1))return false;
 for(int i=0;i<51;i++)if(get(a,h+i)!=g.pc[i])return false;
 for(int i=0;i<h-1;i++)if(get(a,i))return false;
 int pos=h+51;while(pos<2048&&!get(a,pos))pos++;if(pos==2048||pos-h<181)return false;
 pos++;for(int i=0;i<9;i++){if(pos>=2048||get(a,pos))return false;int start=++pos;while(pos<2048&&get(a,pos))pos++;if(pos-start-1!=g.regs[i])return false;}
 int spares=0;while(pos<2048-1){
  if(get(a,pos))return false;if(!get(a,pos+1)){pos++;break;}
  pos++;while(pos<2048&&get(a,pos))pos++;spares++;
 }
 if(spares<167)return false;
 while(pos<2048)if(get(a,pos++))return false;
 return true;
}
bool flex(const Table&T,Case&c,const Goal&g,int start,int finish){Tape tape=c.initial;int h=64,q=start;
 for(int step=1;step<=20000;step++){if(h<0||h>=2048)return false;int b=get(tape,h);Row r=T[q][b];set(tape,h,r.w);h+=r.d;q=r.t;if(q==254)return c.halt;if(!c.halt&&q==finish&&frame(tape,h,g))return true;}return false;}
int main(int argc,char**argv){
 std::ifstream in(argc>1?argv[1]:"candidate245-literal-cases.txt");int nr;in>>nr;Table old{};std::vector<int>states;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}
 int nc;in>>nc;std::vector<Case>cs(nc);std::vector<Goal>goals;
 for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}goals.push_back(goal(c));}
 std::bitset<512>all;int maximum=0;for(int idx=0;idx<nc;idx++){auto&c=cs[idx];if(!execute(old,c,96,96,20000,true)||!flex(old,c,goals[idx],96,96)){std::cerr<<"BASELINE FAILED "<<idx<<"\n";return 1;}all|=c.used;maximum=std::max(maximum,c.steps);}
 std::cerr<<"Baseline "<<nc<<"cases,"<<all.count()<<"rows\n";
 std::vector<int>order(nc);for(int i=0;i<nc;i++)order[i]=i;std::mt19937 rng(20261018);std::shuffle(order.begin(),order.end(),rng);
 int tested=0,survivors=0;long long checks=0;std::ofstream out("flexible-one-action-survivors.txt");auto began=std::chrono::steady_clock::now();
 for(int dead:states){if(dead==96)continue;std::vector<int>incoming;for(int q:states)if(q!=dead)for(int b=0;b<2;b++)if(old[q][b].t==dead)incoming.push_back(q*2+b);if(incoming.size()!=1)continue;int hole=incoming[0],q=hole/2,b=hole%2;std::vector<int>affected;for(int idx:order)if(cs[idx].used[hole])affected.push_back(idx);
  for(int dst:states)if(dst!=dead)for(int w=0;w<2;w++)for(int d:{-1,1}){Table t=old;t[q][b]={w,d,dst};bool good=true;tested++;
   for(int idx:affected){checks++;if(!flex(t,cs[idx],goals[idx],96,96)){good=false;break;}}
   if(good){survivors++;out<<dead<<" "<<q<<" "<<b<<" "<<w<<" "<<d<<" "<<dst<<"\n";out.flush();std::cerr<<"SURVIVOR "<<dead<<" via "<<q<<"/"<<b<<" -> "<<w<<" "<<d<<" "<<dst<<"\n";}
  }
 }
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();std::ofstream sum("flexible-one-action-summary.json");sum<<"{\"candidate_count\":"<<tested<<",\"checks\":"<<checks<<",\"survivors\":"<<survivors<<",\"cases\":"<<nc<<",\"seconds\":"<<seconds<<",\"finite_only\":true,\"scope\":\"Same complete PC and physical registers, arbitrary translation, gap>=181, any >=167 spare blocks\"}\n";std::cerr<<"FINISHED "<<tested<<"recipes "<<survivors<<"survivors seconds "<<seconds<<"\n";
}
