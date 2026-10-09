// Independent differential harness. Reviewed source is included unchanged;
// the oracle enumerates candidate subsets with a byte-array distance ledger,
// recomputing distances directly from coordinates. No clique, coloring, core,
// parity, occupancy, or symmetry pruning is used by the oracle.
#ifndef AUDIT_IMPL
#define AUDIT_IMPL 0
#endif
#define main reviewed_program_main
#if AUDIT_IMPL == 0
#include "reviewed_sources/rainbow_exact_v5.cpp"
#elif AUDIT_IMPL == 1
#include "reviewed_sources/rainbow_edge_prefix.cpp"
#else
#include "reviewed_sources/rainbow_prefix_filtered.cpp"
#endif
#undef main
#include <cassert>
#include <map>
#include <random>

std::mt19937 rng(0x76b514a9u);
std::map<std::pair<int,int>,std::vector<Occupancy>> occupancy_cache;
std::vector<int> values;
long long oracle_nodes=0;
int kernel_checks=0,prefix_checks=0,diameter_checks=0;
int sat_checks=0,unsat_checks=0,max_candidates=0;

int direct_distance(int u,int v){
 int answer=0;
 for(int j=0;j<3;j++){
  int delta=pts[u][j]-pts[v][j];answer+=delta*delta;
 }
 return answer;
}

void setup(int side,int wanted){
 bool same_grid=n==side&&!pts.empty();
 n=side;target=wanted;N=n*n*n;
 max_distance=3*(n-1)*(n-1);limit=1e8;start=Clock::now();
 timeout=false;solution.clear();
 if(!same_grid){
  pts.clear();point_class.clear();
  for(int x=0;x<n;x++)for(int y=0;y<n;y++)for(int z=0;z<n;z++){
   pts.push_back({x,y,z});point_class.push_back((x%2)*4+(y%2)*2+z%2);
  }
  dist.assign(N,vector<int>(N));
  std::set<int> ds;
  for(int i=0;i<N;i++)for(int j=0;j<i;j++)
   ds.insert(dist[i][j]=dist[j][i]=direct_distance(i,j));
  values.assign(ds.begin(),ds.end());
 }
 assert(target*(target-1)/2<=(int)values.size());
 auto key=std::make_pair(n,target);
 if(occupancy_cache.count(key))occupancies=occupancy_cache[key];
 else{
  occupancies.clear();all_occupancies.clear();
  array<int,8> counts{};array<int,4> capacity{};
  for(int d:values)++capacity[d%4];
  generate_occupancies(counts,0,target,capacity);
  occupancy_cache[key]=occupancies;
 }
 all_occupancies.resize(occupancies.size());
 std::iota(all_occupancies.begin(),all_occupancies.end(),0);
}

bool addable(int v,const vector<int>&selected,const array<unsigned char,256>&seen,
             vector<int>&new_distances){
 new_distances.clear();
 for(int u:selected){
  int d=direct_distance(u,v);
  if(d<=0||d>max_distance||seen[d]||
      std::find(new_distances.begin(),new_distances.end(),d)!=new_distances.end())return false;
  new_distances.push_back(d);
 }
 return true;
}

bool oracle_rec(const vector<int>&pool,int first,vector<int>&selected,
                 array<unsigned char,256>&seen){
 ++oracle_nodes;
 int need=target-(int)selected.size();
 if(need==0)return true;
 if((int)pool.size()-first<need)return false;
 for(int at=first;at+need<=(int)pool.size();at++){
  vector<int> fresh;
  if(!addable(pool[at],selected,seen,fresh))continue;
  for(int d:fresh)seen[d]=1;
  selected.push_back(pool[at]);
  if(oracle_rec(pool,at+1,selected,seen))return true;
  selected.pop_back();
  for(int d:fresh)seen[d]=0;
 }
 return false;
}

array<unsigned char,256> ledger(const vector<int>&selected){
 array<unsigned char,256> seen{};
 for(int i=0;i<(int)selected.size();i++)for(int j=0;j<i;j++){
  int d=direct_distance(selected[i],selected[j]);
  assert(d>0&&!seen[d]);seen[d]=1;
 }
 return seen;
}

bool oracle(const vector<int>&pool,const vector<int>&chosen){
 auto selected=chosen;auto seen=ledger(selected);
 return oracle_rec(pool,0,selected,seen);
}

Mask encode_used(const vector<int>&selected){
 auto seen=ledger(selected);Mask used;
 for(int d=1;d<256;d++)if(seen[d])used.set(d);
 return used;
}

vector<Candidate> candidates(const vector<int>&pool,const vector<int>&selected){
 vector<Candidate> answer;auto seen=ledger(selected);
 for(int v:pool){
  vector<int> fresh;
  if(!addable(v,selected,seen,fresh))continue;
  Candidate c;c.v=v;for(int d:fresh)c.radial.set(d);answer.push_back(c);
 }
 return answer;
}

void check_witness(const vector<int>&allowed,const vector<int>&selected){
 assert((int)solution.size()==target);
 auto seen=ledger(solution);(void)seen;
 for(int v:selected)assert(find(solution.begin(),solution.end(),v)!=solution.end());
 for(int v:solution)assert(find(selected.begin(),selected.end(),v)!=selected.end()||
                         find(allowed.begin(),allowed.end(),v)!=allowed.end());
 auto prior=ledger(selected);
 for(int i=0;i<target;i++)for(int j=0;j<i;j++){
  int d=direct_distance(solution[i],solution[j]);
  assert(prior[d]||d<=max_distance);
 }
}

void check_kernel(const vector<int>&selected,vector<Candidate> c){
 vector<int> pool;for(const auto&r:c)pool.push_back(r.v);
 bool expected=oracle(pool,selected);
 auto chosen=selected;solution.clear();
 bool actual=search(c,encode_used(selected),chosen,all_occupancies);
 if(expected!=actual){
  cerr<<"KERNEL MISMATCH n="<<n<<" target="<<target<<" s="<<selected.size()
      <<" c="<<c.size()<<" expected="<<expected<<" actual="<<actual<<"\n";
  abort();
 }
 assert(!timeout);
 if(actual){check_witness(pool,selected);++sat_checks;}else ++unsat_checks;
 ++kernel_checks;max_candidates=max(max_candidates,(int)c.size());
}

void random_kernel_checks(){
 const int sides[]={2,3,4,5,7,8,10};
 for(int test=0;test<1800;test++){
  int side=sides[test*7/1800];
  int max_target=side==2?3:side==3?4:min(side+2,9);
  int wanted=2+rng()%(max_target-1);
  setup(side,wanted);
  vector<int> order(N);iota(order.begin(),order.end(),0);
  shuffle(order.begin(),order.end(),rng);
  vector<int> selected;array<unsigned char,256> seen{};
  int selected_goal=1+rng()%min(wanted,4);
  for(int v:order){
   vector<int> fresh;
   if(!addable(v,selected,seen,fresh))continue;
   selected.push_back(v);for(int d:fresh)seen[d]=1;
   if((int)selected.size()==selected_goal)break;
  }
  // A cap below some already-selected distances also tests prefix-style
  // states, whose used ledger is allowed to contain earlier long edges.
  if(test%3==0)max_distance=1+rng()%max_distance;
  auto c=candidates(order,selected);
  shuffle(c.begin(),c.end(),rng);
  c.resize(min(c.size(),size_t(rng()%19)));
  check_kernel(selected,c);
 }
 // Exercise every vertex-mask word, including the highest allowed index.
 for(int side:{7,8,10})for(int wanted:{3,4}){
  setup(side,wanted);
  vector<int> order(N);iota(order.begin(),order.end(),0);
  vector<int> selected{0};auto c=candidates(order,selected);
  check_kernel(selected,c);
 }
}

void witness_based_checks(){
 const vector<array<int,3>> witness7={{0,0,0},{2,0,0},{0,6,0},{6,1,2},{4,2,0},
                                   {6,1,3},{3,6,6},{5,1,5},{6,4,6},{4,5,5}};
 const vector<array<int,3>> witness8={{7,4,0},{2,0,1},{7,0,0},{0,7,7},{2,5,7},{7,3,0},
                                   {7,7,7},{1,5,6},{4,7,3},{3,1,7},{5,0,0},{4,1,1}};
 for(int side:{7,8})for(int extra:{0,1})for(int test=0;test<24;test++){
  const auto&witness=side==7?witness7:witness8;
  setup(side,witness.size()+extra);
  vector<int> ids;for(auto p:witness)ids.push_back((p[0]*n+p[1])*n+p[2]);
  (void)ledger(ids);
  shuffle(ids.begin(),ids.end(),rng);
  int selected_size=3+test%6;
  vector<int> selected(ids.begin(),ids.begin()+selected_size);
  vector<int> order(N);iota(order.begin(),order.end(),0);shuffle(order.begin(),order.end(),rng);
  auto noise=candidates(order,selected);
  vector<int> pool(ids.begin()+selected_size,ids.end());
  for(auto c:noise)if(find(pool.begin(),pool.end(),c.v)==pool.end()){
   pool.push_back(c.v);if(pool.size()>=22)break;
  }
  check_kernel(selected,candidates(pool,selected));
 }
}

void small_diameter_checks(){
 for(auto specification:{pair<int,int>{2,3},{3,3},{3,4},{4,5},{4,6}}){
  setup(specification.first,specification.second);
  int threshold=values[target*(target-1)/2-1];
  vector<int> entire(N);iota(entire.begin(),entire.end(),0);
  for(int p=0;p<N;p++)for(int q=p+1;q<N;q++){
   if(dist[p][q]<threshold)continue;
   // Selecting orbit representatives is not needed for this differential
   // test; every eligible unordered diameter pair is tested.
   int diameter=dist[p][q];max_distance=diameter;
   vector<int> chosen{p,q};auto c=candidates(entire,chosen);
   vector<int> pool;for(const auto&r:c)pool.push_back(r.v);
   bool expected=oracle(pool,chosen);
   auto selected=chosen;solution.clear();
   bool actual=search_diameter(c,encode_used(chosen),selected);
   if(expected!=actual){cerr<<"DIAMETER MISMATCH "<<n<<" "<<target<<" "<<p<<" "<<q<<"\n";abort();}
   if(actual)check_witness(pool,chosen);
   ++diameter_checks;
#if AUDIT_IMPL != 0
   for(int depth=2;depth<=6;depth++){
    max_distance=diameter;solution.clear();
    actual=search_top_two(c,values,p,q,depth);
    if(expected!=actual){cerr<<"PREFIX MISMATCH "<<n<<" "<<target<<" "<<p<<" "<<q<<" depth="<<depth<<"\n";abort();}
    if(actual){max_distance=diameter;check_witness(pool,chosen);}
    assert(!timeout);++prefix_checks;
   }
#endif
  }
 }
}

int main(){
 random_kernel_checks();witness_based_checks();small_diameter_checks();
 cout<<"{\"implementation\":"<<AUDIT_IMPL<<",\"kernel_checks\":"<<kernel_checks
     <<",\"kernel_sat\":"<<sat_checks<<",\"kernel_unsat\":"<<unsat_checks
     <<",\"maximum_candidate_count\":"<<max_candidates
     <<",\"diameter_checks\":"<<diameter_checks
     <<",\"prefix_checks\":"<<prefix_checks
     <<",\"oracle_nodes\":"<<oracle_nodes<<",\"result\":\"all comparisons agree\"}\n";
}
