#define main anneal_main
#include "association_search193.cpp"
#undef main
#include <unordered_set>
#include <deque>
struct Point {vector<pair<int,int>> sh; Stat s;};
uint64_t hashshape(const vector<pair<int,int>>&v) {uint64_t h=0x7777712345678911ULL;for(auto p:v){h^=(p.first+444)*7654684743222533ULL;h=(h<<13)|(h>>51);h^=(p.second+555)*6144392410144313ULL;h=(h<<17)|(h>>47);}return h;}
int main(int argc,char**argv){
 init(argv[1]); rng.seed(argc>5?strtoull(argv[5],0,10):777111);
 int budget=argc>3?stoi(argv[3]):100000;int cap=argc>4?stoi(argv[4]):20000;
 Meta m;vector<Point>pool;
 unordered_set<uint64_t>seen;seen.reserve(10000000);
 auto add=[&](const vector<pair<int,int>>&sh){shape=sh;auto s=score(m);cout<<"INIT "<<s.eff<<" "<<s.n<<" "<<s.fold<<" "<<s.pen<<endl;pool.push_back({sh,s});seen.insert(hashshape(sh));};
 add(shape);if(argc>2){ifstream f(argv[2]);vector<pair<int,int>>sh;int a,b;while(f>>a>>b)sh.push_back({a,b});add(sh);}
 auto start=chrono::steady_clock::now();int parents=0;long long tries=0,retained=0;int low_n=100;
 while(!pool.empty()&&parents<budget){
  int ix=rng()%pool.size();Point cur=move(pool[ix]);pool[ix]=move(pool.back());pool.pop_back();parents++;
  shape=cur.sh;score(m);int nc=ncanon;
  vector<pair<int,int>> moves;
  for(int t=nt;t<nc;t++){if(leftid[t]>=nt)moves.push_back({t,0});if(rightid[t]>=nt)moves.push_back({t,1});}
  for(int t=nw;t<nw+np;t++){if(shape[t-nw].first>=nw)moves.push_back({t,2});if(shape[t-nw].second>=nw)moves.push_back({t,3});}
  shuffle(moves.begin(),moves.end(),rng);
  for(auto [t,d]:moves){
   shape=cur.sh;score(m);auto trial=rotated(t,d%2,d>=2);
   uint64_t h=hashshape(trial);if(!seen.insert(h).second)continue;
   shape=trial;Stat s=score(m);tries++;
   if(s.pen==0&&s.eff<=59){savecandidate("beam_winner.json",m,s,parents,tries,trial);cout<<"WIN "<<s.eff<<" "<<s.n<<" "<<s.fold<<endl;return 0;}
   if(s.pen==0&&s.eff==60){
    retained++;if(s.n<low_n){low_n=s.n;savecandidate("beam_small_raw.json",m,s,parents,tries,trial);}
    if(int(pool.size())<cap)pool.push_back({move(trial),s});else if(rng()%4==0)pool[rng()%pool.size()]={move(trial),s};
    if(retained%1000==0){savecandidate("beam_last.json",m,s,parents,tries,shape);}
   }
  }
  if(parents%100==0){auto sec=chrono::duration<double>(chrono::steady_clock::now()-start).count();cout<<"PROGRESS parents="<<parents<<" tried="<<tries<<" retained="<<retained<<" pool="<<pool.size()<<" seen="<<seen.size()<<" lowest_raw="<<low_n<<" secs="<<sec<<endl;}
 }
 cout<<"DONE parents="<<parents<<" tried="<<tries<<" retained="<<retained<<" pool="<<pool.size()<<" seen="<<seen.size()<<endl;
 for(int i=0;i<min(10,int(pool.size()));i++){string n="beam_seed"+to_string(i)+".json";savecandidate(n.c_str(),m,pool[i].s,parents,tries,pool[i].sh);}
}
