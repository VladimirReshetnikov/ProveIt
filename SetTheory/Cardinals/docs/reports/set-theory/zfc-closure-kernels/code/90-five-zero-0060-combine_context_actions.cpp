// Joint context-sensitive elimination with execution-directed finite search.
#define main inherited_pair_main
#include "pair_merge_search.cpp"
#undef main
std::array<uint64_t,256*2048>no_write_seen{};uint64_t epoch=0;
struct Hole{int q,b;std::vector<Row>choices;};
struct Search{
 Table old;std::vector<Case>*cs;std::vector<int>cases;std::vector<Hole>holes;std::array<int,512>index;std::vector<int>choice;int dead,found=0,limit=5;bool aborted=false;long long step_budget=100000000,call_budget=50000;long long calls=0,steps=0,failures=0;double starttime;
 bool rec(int ci,Tape tape,int q,int h,int tick){
  calls++;if(calls>call_budget){aborted=true;return true;}if(calls%100000==0)std::cerr<<"progress dead="<<dead<<" calls="<<calls<<" found="<<found<<"\n";
  auto token=++epoch;
  while(ci<(int)cases.size()){
   Case &c=(*cs)[cases[ci]];
   while(tick<20000){
    if(steps>=step_budget){aborted=true;return true;}
    if(h<0||h>=2048){failures++;return false;}
    int pos=q*2048+h;if(no_write_seen[pos]==token){failures++;return false;}no_write_seen[pos]=token;
    int b=get(tape,h),k=index[2*q+b];
    if(k>=0&&choice[k]<0){
     for(int a=0;a<(int)holes[k].choices.size();a++){choice[k]=a;if(rec(ci,tape,q,h,tick)){choice[k]=-1;return true;}}
     choice[k]=-1;return false;
    }
    Row r=k>=0?holes[k].choices[choice[k]]:old[q][b];
    if(r.w!=b)token=++epoch;
    set(tape,h,r.w);h+=r.d;q=r.t;tick++;steps++;
    if(q==254){if(!c.halt){failures++;return false;}break;}
    if(!c.halt&&q==96&&h==64+c.head&&tape==c.target)break;
   }
   if(tick>=20000){failures++;return false;}
   ci++;if(ci<(int)cases.size()){tape=(*cs)[cases[ci]].initial;q=96;h=64;tick=0;token=++epoch;}
  }
  found++;
  Table result=old;for(int k=0;k<(int)holes.size();k++)result[holes[k].q][holes[k].b]=holes[k].choices[std::max(0,choice[k])];
  std::string filename="candidate244-context-"+std::to_string(dead)+"-"+std::to_string(found)+"-old.tm";std::ofstream out(filename);out<<"#! start 95\n";for(int a=0;a<256;a++)if(a!=dead&&old[a][0].t)for(int b=0;b<2;b++){auto r=result[a][b];out<<a<<" "<<b<<" "<<r.w<<" "<<(r.d==1?'R':'L')<<" "<<r.t<<"\n";}
  std::cerr<<"FOUND "<<filename<<"\n";
  for(int k=0;k<(int)holes.size();k++){auto r=result[holes[k].q][holes[k].b];std::cerr<<holes[k].q<<"/"<<holes[k].b<<" -> "<<r.w<<" "<<r.d<<" "<<r.t<<"\n";}
  return found>=limit;
 }
 void run(){index.fill(-1);choice.assign(holes.size(),-1);for(int k=0;k<(int)holes.size();k++)index[2*holes[k].q+holes[k].b]=k;
  for(int i=0;i<(int)cs->size();i++){bool used=false;for(auto&hole:holes)if((*cs)[i].used[hole.q*2+hole.b])used=true;if(used)cases.push_back(i);}
  std::array<int,512>freq{};for(int i:cases)for(auto&hole:holes)if((*cs)[i].used[hole.q*2+hole.b])freq[hole.q*2+hole.b]++;
  auto rarity=[&](int i){double score=0;for(auto&hole:holes)if((*cs)[i].used[hole.q*2+hole.b])score+=1.0/freq[hole.q*2+hole.b];return score;};
  std::stable_sort(cases.begin(),cases.end(),[&](int a,int b){double x=rarity(a),y=rarity(b);return x!=y?x>y:(*cs)[a].steps<(*cs)[b].steps;});
  std::cerr<<"START dead="<<dead<<" holes="<<holes.size()<<" cases="<<cases.size()<<" domains=";for(auto&hole:holes)std::cerr<<hole.choices.size()<<",";std::cerr<<"\n";
  rec(0,(*cs)[cases[0]].initial,96,64,0);
  std::cerr<<"END dead="<<dead<<" found="<<found<<" calls="<<calls<<" steps="<<steps<<" aborted="<<aborted<<" failures="<<failures<<"\n";
 }
};
int main(int argc,char**argv){std::ifstream in(argc>1?argv[1]:"candidate245-literal-cases.txt");int nr;in>>nr;Table old{};std::vector<int>states;for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;old[q][b]=r;if(!b)states.push_back(q);}int nc;in>>nc;std::vector<Case>cs(nc);for(auto&c:cs){int flag,n,x;in>>flag>>c.head>>n;c.halt=flag;for(int j=0;j<n;j++){in>>x;set(c.initial,x+64,1);}in>>n;for(int j=0;j<n;j++){in>>x;set(c.target,x+64,1);}}
 for(auto&c:cs)if(!execute(old,c,96,96,20000,true))throw 1;
 std::ifstream opts(argc>2?argv[2]:"context-action-options.txt");std::array<std::vector<Row>,512>options;int q,b,dead,w,d,t;while(opts>>q>>b>>dead>>w>>d>>t)options[2*q+b].push_back({w,d,t});
 std::ofstream summary("context-combination-summary.jsonl");
 for(int dead:states){if(dead==95||dead==96)continue;Search s;s.old=old;s.cs=&cs;s.dead=dead;bool good=true;for(int q:states)if(q!=dead)for(int b=0;b<2;b++)if(old[q][b].t==dead){s.holes.push_back({q,b,options[2*q+b]});if(options[2*q+b].empty())good=false;}
  if(!good||s.holes.empty())continue;s.run();summary<<"{\"dead\":"<<dead<<",\"holes\":"<<s.holes.size()<<",\"affected_cases\":"<<s.cases.size()<<",\"found\":"<<s.found<<",\"calls\":"<<s.calls<<",\"literal_steps\":"<<s.steps<<",\"complete\":"<<(s.aborted?"false":"true")<<",\"literal_step_budget\":"<<s.step_budget<<",\"branch_call_budget\":"<<s.call_budget<<",\"finite_only\":true}\n";summary.flush();
 }
}
