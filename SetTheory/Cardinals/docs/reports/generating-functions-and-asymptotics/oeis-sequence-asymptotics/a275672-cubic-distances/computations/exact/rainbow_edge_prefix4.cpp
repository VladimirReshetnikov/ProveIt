// Exact, symmetry-reduced rainbow-clique search in [0,n-1]^3.
// Compile: g++ -O3 -std=c++17 rainbow_exact.cpp -o rainbow_exact
// Usage: ./rainbow_exact n target time_limit_seconds [anchor_index]
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <vector>
using namespace std;
using U=uint64_t;
using Clock=chrono::steady_clock;
#ifndef USE_MOD4
#define USE_MOD4 1
#endif
#ifndef USE_PAIR_STABILIZER
#define USE_PAIR_STABILIZER 1
#endif
const int W=16; // up to 1024 vertices, n<=10
struct Bits {
 array<U,W> a{};
 void set(int i){a[i/64]|=U(1)<<(i%64);}
 void reset(int i){a[i/64]&=~(U(1)<<(i%64));}
 bool test(int i)const{return a[i/64]>>(i%64)&1;}
 bool empty()const{for(U x:a)if(x)return false;return true;}
 int first()const{for(int i=0;i<W;i++)if(a[i])return 64*i+__builtin_ctzll(a[i]);return -1;}
 Bits operator&(const Bits&b)const{Bits r;for(int i=0;i<W;i++)r.a[i]=a[i]&b.a[i];return r;}
 void exclude(const Bits&b){for(int i=0;i<W;i++)a[i]&=~b.a[i];}
};
struct Mask {
 array<U,4>a{};
 bool has(int d)const{return a[d/64]>>(d%64)&1;}
 void set(int d){a[d/64]|=U(1)<<(d%64);}
 bool meets(const Mask&b)const{for(int i=0;i<4;i++)if(a[i]&b.a[i])return true;return false;}
 Mask operator|(const Mask&b)const{Mask r;for(int i=0;i<4;i++)r.a[i]=a[i]|b.a[i];return r;}
 int count()const{int r=0;for(U w:a)r+=__builtin_popcountll(w);return r;}
 int oddcount()const{int r=0;for(U w:a)r+=__builtin_popcountll(w&0xaaaaaaaaaaaaaaaaULL);return r;}
};
struct Candidate{int v;Mask radial;};
int n,target,N,max_distance;
vector<array<int,3>>pts;
vector<vector<int>>dist;
vector<int>solution;
struct Occupancy{array<int,8>count;array<int,4>requirements;};
vector<Occupancy>occupancies;
vector<int>all_occupancies;
vector<int>point_class;
Clock::time_point start;
double limit;
uint64_t nodes=0,colors_pruned=0;
bool timeout=false;
double elapsed(){return chrono::duration<double>(Clock::now()-start).count();}

bool search(vector<Candidate>&c,Mask used,vector<int>&chosen,const vector<int>&parent_occupancies){
 ++nodes;
 if((nodes&16383)==0&&elapsed()>limit){timeout=true;return false;}
 int need=target-(int)chosen.size(),m=c.size();
 if(need==0){solution=chosen;return true;}
 if(m<need)return false;
 if(need==1){solution=chosen;solution.push_back(c[0].v);return true;}
 // The compatibility graph depends on the entire selected set.
 vector<Bits>adj(m);
 Mask available=used,radial;
 int parities[2]={0,0},selected_parities[2]={0,0};
 for(auto&q:c){available=available|q.radial;radial=radial|q.radial;
  auto p=pts[q.v];++parities[(p[0]+p[1]+p[2])%2];}
 for(int v:chosen){auto p=pts[v];++selected_parities[(p[0]+p[1]+p[2])%2];}
 if(radial.count()<(int)chosen.size()*need)return false;
 for(int i=0;i<m;i++)for(int j=0;j<i;j++){
  int d=dist[c[i].v][c[j].v];
  if(d<=max_distance&&!used.has(d)&&!c[i].radial.has(d)&&!c[j].radial.has(d)&&
      !c[i].radial.meets(c[j].radial)){
   adj[i].set(j);adj[j].set(i);
   available.set(d);
  }
 }
 if(available.count()<target*(target-1)/2)return false;
 int odd=available.oddcount(),even=available.count()-odd;
 bool parity_possible=false;
 for(int add0=0;add0<=need;add0++){
  int add1=need-add0;
  if(add0>parities[0]||add1>parities[1])continue;
  int required_odd=(selected_parities[0]+add0)*(selected_parities[1]+add1);
  if(required_odd<=odd&&target*(target-1)/2-required_odd<=even){parity_possible=true;break;}
 }
 if(!parity_possible)return false;
 vector<int>possible_occupancies;
#if USE_MOD4
 array<int,8>selected_count{},candidate_count{};
 for(int v:chosen)++selected_count[point_class[v]];
 for(auto&q:c)++candidate_count[point_class[q.v]];
 array<int,4>capacity{};
 for(int residue=0;residue<4;residue++)for(U w:available.a)
  capacity[residue]+=__builtin_popcountll(w&(0x1111111111111111ULL<<residue));
 for(int id:parent_occupancies){
  const auto&o=occupancies[id];bool good=true;
  for(int r=0;r<4;r++)if(o.requirements[r]>capacity[r]){good=false;break;}
  if(good)for(int r=0;r<8;r++)if(o.count[r]<selected_count[r]||o.count[r]>selected_count[r]+candidate_count[r]){good=false;break;}
  if(good)possible_occupancies.push_back(id);
 }
 if(possible_occupancies.empty())return false;
#endif
 // Greedy proper coloring supplies a certified clique upper bound.
 // Degrees are sorted to improve coloring, without discarding vertices.
 vector<int>degree(m);
 for(int i=0;i<m;i++)for(U w:adj[i].a)degree[i]+=__builtin_popcountll(w);
 vector<char>alive(m,1);vector<int>queue;
 for(int i=0;i<m;i++)if(degree[i]<need-1)queue.push_back(i);
 for(int at=0;at<(int)queue.size();at++){
  int v=queue[at];if(!alive[v])continue;alive[v]=0;
  Bits neighbors=adj[v];
  while(!neighbors.empty()){
   int j=neighbors.first();neighbors.reset(j);
   if(alive[j]&&--degree[j]==need-2)queue.push_back(j);
  }
 }
 vector<int>idx;for(int i=0;i<m;i++)if(alive[i])idx.push_back(i);
 if((int)idx.size()<need)return false;
 stable_sort(idx.begin(),idx.end(),[&](int i,int j){return degree[i]>degree[j];});
 vector<int>order,bound;
 Bits remain;
 for(int i:idx)remain.set(i);
 int color=0;
 while(!remain.empty()){
  ++color;
  Bits avail=remain;
  for(int v:idx)if(avail.test(v)){
   order.push_back(v);bound.push_back(color);
   remain.reset(v);avail.reset(v);avail.exclude(adj[v]);
  }
 }
 if(color<need){++colors_pruned;return false;}
 Bits active;for(int i:idx)active.set(i);
 for(int oi=(int)order.size()-1;oi>=0;oi--){
  if(bound[oi]<need){++colors_pruned;return false;}
  int v=order[oi];
  Bits nextbits=active&adj[v];
  vector<Candidate>next;
  while(!nextbits.empty()){
   int j=nextbits.first();nextbits.reset(j);
   Candidate q=c[j];q.radial.set(dist[c[v].v][q.v]);next.push_back(q);
  }
  if((int)next.size()>=need-1){
   chosen.push_back(c[v].v);
   if(search(next,used|c[v].radial,chosen,possible_occupancies))return true;
   chosen.pop_back();
   if(timeout)return false;
  }
  active.reset(v);
 }
 return false;
}
void generate_occupancies(array<int,8>&counts,int at,int remaining,const array<int,4>&capacity){
 if(at<7){for(int x=0;x<=remaining;x++){counts[at]=x;generate_occupancies(counts,at+1,remaining-x,capacity);}return;}
 counts[7]=remaining;array<int,4>r{};
 for(int i=0;i<8;i++)r[0]+=counts[i]*(counts[i]-1)/2;
 for(int i=0;i<8;i++)for(int j=0;j<i;j++)r[__builtin_popcount(i^j)]+=counts[i]*counts[j];
 for(int i=0;i<4;i++)if(r[i]>capacity[i])return;
 all_occupancies.push_back(occupancies.size());occupancies.push_back({counts,r});
}

array<int,3> representative(array<int,3>p){
 for(int&i:p)i=min(i,n-1-i);
 sort(p.begin(),p.end());return p;
}
array<int,6> pair_representative(array<int,3>p,array<int,3>q){
 array<int,6>best;best.fill(n);
 array<int,3>perm{0,1,2};
 do{
  for(int flip=0;flip<8;flip++){
   array<int,3>a,b;
   for(int k=0;k<3;k++){
    a[k]=(flip>>k&1)?n-1-p[perm[k]]:p[perm[k]];
    b[k]=(flip>>k&1)?n-1-q[perm[k]]:q[perm[k]];
   }
   if(b<a)swap(a,b);
   array<int,6>r{a[0],a[1],a[2],b[0],b[1],b[2]};
   if(r<best)best=r;
  }
 }while(next_permutation(perm.begin(),perm.end()));
 return best;
}
bool search_diameter(vector<Candidate>&c,Mask used,vector<int>&chosen){
#if USE_PAIR_STABILIZER
 if(target<=3)return search(c,used,chosen,all_occupancies);
 // After fixing the unique diameter edge, its setwise stabilizer still
 // acts on the remaining points.  Canonicalize their lexicographic first
 // member exactly as for the single-point cube anchors.
 vector<vector<int>>maps;
 array<int,3>perm{0,1,2};int p=chosen[0],q=chosen[1];
 do{for(int flip=0;flip<8;flip++){
  auto transform=[&](int v){int r=0;for(int k=0;k<3;k++)r=n*r+((flip>>k&1)?n-1-pts[v][perm[k]]:pts[v][perm[k]]);return r;};
  int a=transform(p),b=transform(q);
  if(!((a==p&&b==q)||(a==q&&b==p)))continue;
  vector<int>map(N);for(int i=0;i<N;i++)map[i]=transform(i);maps.push_back(map);
 }}while(next_permutation(perm.begin(),perm.end()));
 if(maps.size()>=2){
  vector<int>rep(N);iota(rep.begin(),rep.end(),0);
  for(const auto&map:maps)for(int v=0;v<N;v++)rep[v]=min(rep[v],map[v]);
  for(const auto&r:c)if(rep[r.v]==r.v){
   vector<Candidate>next;
   for(const auto&s:c)if(s.v>r.v&&rep[s.v]>=r.v){
    int d=dist[r.v][s.v];
    if(d>max_distance||used.has(d)||r.radial.has(d)||s.radial.has(d)||r.radial.meets(s.radial))continue;
    Candidate t=s;t.radial.set(d);next.push_back(t);
   }
   if((int)next.size()<target-3)continue;
   chosen.push_back(r.v);
   if(search(next,used|r.radial,chosen,all_occupancies))return true;
   chosen.pop_back();if(timeout)return false;
  }
  return false;
 }
#endif
 return search(c,used,chosen,all_occupancies);
}
bool extend_edge_prefix(const vector<Candidate>&initial,const vector<int>&selected,
                        Mask used,Mask processed,int previous,int remaining,
                        const vector<int>&distance_values,
                        const vector<vector<int>>&maps,const vector<int>&active_maps){
 if(remaining==0||(int)selected.size()==target){
  auto c=initial;auto chosen=selected;max_distance=previous;
  return search(c,used,chosen,all_occupancies);
 }
 int rank=processed.count()+1;
 int lower=distance_values[target*(target-1)/2-rank];
 for(int d=previous-1;d>=lower;d--)if(used.has(d)&&!processed.has(d)){lower=d;break;}
 vector<int>pool=selected;for(auto&r:initial)pool.push_back(r.v);sort(pool.begin(),pool.end());
 for(int ui=0;ui<(int)pool.size();ui++)for(int vi=ui+1;vi<(int)pool.size();vi++){
  int u=pool[ui],v=pool[vi],next_length=dist[u][v];
  if(next_length<lower||next_length>=previous)continue;
  bool canonical=true;
  for(int map_id:active_maps){const auto&map=maps[map_id];
   int a=map[u],b=map[v];if(a>b)swap(a,b);
   if(a<u||(a==u&&b<v)){canonical=false;break;}
  }
  if(!canonical)continue;
  if(elapsed()>limit){timeout=true;return false;}
  vector<int>chosen=selected;
  if(find(chosen.begin(),chosen.end(),u)==chosen.end())chosen.push_back(u);
  if(find(chosen.begin(),chosen.end(),v)==chosen.end())chosen.push_back(v);
  if((int)chosen.size()>target)continue;
  Mask next_used;bool valid=true;
  for(int i=0;i<(int)chosen.size()&&valid;i++)for(int j=0;j<i;j++){
   int d=dist[chosen[i]][chosen[j]];
   if(next_used.has(d)||(d>next_length&&!processed.has(d))){valid=false;break;}
   next_used.set(d);
  }
  if(!valid)continue;
  vector<Candidate>c;
  for(const auto&old:initial){int w=old.v;
   if(find(chosen.begin(),chosen.end(),w)!=chosen.end())continue;
   Candidate r;r.v=w;bool good=true;
   for(int a:chosen){int d=dist[a][w];
    if(d>next_length||next_used.has(d)||r.radial.has(d)){good=false;break;}
    r.radial.set(d);
   }
   if(good)c.push_back(r);
  }
  if((int)c.size()<target-(int)chosen.size())continue;
  Mask next_processed=processed;next_processed.set(next_length);
  vector<int>next_maps;
  for(int map_id:active_maps){int a=maps[map_id][u],b=maps[map_id][v];
   if((a==u&&b==v)||(a==v&&b==u))next_maps.push_back(map_id);
  }
  if(extend_edge_prefix(c,chosen,next_used,next_processed,next_length,remaining-1,
                       distance_values,maps,next_maps))return true;
  if(timeout)return false;
 }
 return false;
}
bool search_top_two(vector<Candidate>&initial,const vector<int>&distance_values,
                    int p,int q,int prefix_length){
 int diameter=dist[p][q];
 int threshold=distance_values[target*(target-1)/2-2];
 vector<int>pool{p,q};for(auto&r:initial)pool.push_back(r.v);
 sort(pool.begin(),pool.end());
 vector<vector<int>>maps;
 array<int,3>perm{0,1,2};
 do{for(int flip=0;flip<8;flip++){
  auto transform=[&](int v){int r=0;for(int k=0;k<3;k++)r=n*r+((flip>>k&1)?n-1-pts[v][perm[k]]:pts[v][perm[k]]);return r;};
  int a=transform(p),b=transform(q);
  if(!((a==p&&b==q)||(a==q&&b==p)))continue;
  vector<int>map(N);for(int i=0;i<N;i++)map[i]=transform(i);maps.push_back(map);
 }}while(next_permutation(perm.begin(),perm.end()));
 for(int ui=0;ui<(int)pool.size();ui++)for(int vi=ui+1;vi<(int)pool.size();vi++){
  int u=pool[ui],v=pool[vi],second=dist[u][v];
  if(second<threshold||second>=diameter)continue;
  bool canonical=true;
  for(auto&map:maps){
   int a=map[u],b=map[v];if(a>b)swap(a,b);
   if(a<u||(a==u&&b<v)){canonical=false;break;}
  }
  if(!canonical)continue;
  vector<int>chosen{p,q};
  if(u!=p&&u!=q)chosen.push_back(u);
  if(v!=p&&v!=q)chosen.push_back(v);
  if((int)chosen.size()>target)continue;
  Mask used;bool valid=true;
  for(int i=0;i<(int)chosen.size()&&valid;i++)for(int j=0;j<i;j++){
   int d=dist[chosen[i]][chosen[j]];
   if(used.has(d)||(i!=1&&d>second)){valid=false;break;}
   used.set(d);
  }
  if(!valid)continue;
  vector<Candidate>c;
  for(int w=0;w<N;w++){
   if(find(chosen.begin(),chosen.end(),w)!=chosen.end())continue;
   Candidate r;r.v=w;bool good=true;
   for(int a:chosen){int d=dist[a][w];
    if(d>second||used.has(d)||r.radial.has(d)){good=false;break;}
    r.radial.set(d);
   }
   if(good)c.push_back(r);
  }
  max_distance=second;
  Mask processed;processed.set(diameter);processed.set(second);
  vector<int>active_maps;
  for(int i=0;i<(int)maps.size();i++){
   int a=maps[i][u],b=maps[i][v];
   if((a==u&&b==v)||(a==v&&b==u))active_maps.push_back(i);
  }
  if(extend_edge_prefix(c,chosen,used,processed,second,prefix_length-2,
                       distance_values,maps,active_maps))return true;
  if(timeout)return false;
 }
 max_distance=diameter;return false;
}
void print_witness(const string&scope,int index){
 cout<<"{\"n\":"<<n<<",\"target\":"<<target<<",\"status\":\"SAT\",\"scope\":\""<<scope<<"\",\"case_index\":"<<index<<",\"points\":[";
 for(int j=0;j<(int)solution.size();j++){
  if(j)cout<<",";auto p=pts[solution[j]];cout<<"["<<p[0]<<","<<p[1]<<","<<p[2]<<"]";
 }
 cout<<"],\"nodes\":"<<nodes<<",\"seconds\":"<<elapsed()<<"}\n";
}
int main(int argc,char**argv){
 if(argc<4){cerr<<"Usage: n target seconds [anchor_index | diameters [case_index]]\n";return 2;}
 n=atoi(argv[1]);target=atoi(argv[2]);limit=atof(argv[3]);
 if(n<1||n>10||target<1)return 2;
 max_distance=3*(n-1)*(n-1);
 start=Clock::now();
 for(int x=0;x<n;x++)for(int y=0;y<n;y++)for(int z=0;z<n;z++)pts.push_back({x,y,z});
 N=pts.size();dist.assign(N,vector<int>(N));
 for(auto p:pts)point_class.push_back((p[0]%2)*4+(p[1]%2)*2+p[2]%2);
 for(int i=0;i<N;i++)for(int j=0;j<i;j++){
  int d=0;for(int a=0;a<3;a++)d+=(pts[i][a]-pts[j][a])*(pts[i][a]-pts[j][a]);
  dist[i][j]=dist[j][i]=d;
 }
 set<int>distance_set;
 for(int i=0;i<N;i++)for(int j=0;j<i;j++)distance_set.insert(dist[i][j]);
 if(target*(target-1)/2>(int)distance_set.size()){
  cout<<"{\"n\":"<<n<<",\"target\":"<<target<<",\"status\":\"UNSAT\",\"scope\":\"global_distance_count\",\"nodes\":0,\"seconds\":"<<elapsed()<<"}\n";return 0;
 }
#if USE_MOD4
 array<int,4>capacity{};for(int d:distance_set)++capacity[d%4];
 array<int,8>initial_counts{};generate_occupancies(initial_counts,0,target,capacity);
 if(all_occupancies.empty()){
  cout<<"{\"n\":"<<n<<",\"target\":"<<target<<",\"status\":\"UNSAT\",\"scope\":\"global_mod4_occupancies\",\"nodes\":0,\"seconds\":"<<elapsed()<<"}\n";return 0;
 }
#endif
 if(argc>4&&(string(argv[4])=="diameters"||string(argv[4])=="top2"||string(argv[4])=="top3"||string(argv[4])=="top4")){
  bool top2=string(argv[4])!="diameters";
  int prefix_length=top2?(argv[4][3]-'0'):1;
  if(target<2||(top2&&target<3)){cerr<<"Diameter mode requires target>=2; top2 requires target>=3\n";return 2;}
  vector<int>distance_values(distance_set.begin(),distance_set.end());
  int threshold=distance_values[target*(target-1)/2-1];
  vector<pair<int,int>>cases;
  for(int i=0;i<N;i++)for(int j=i+1;j<N;j++)if(dist[i][j]>=threshold){
   auto p=pts[i],q=pts[j];
   array<int,6>r{p[0],p[1],p[2],q[0],q[1],q[2]};
   if(pair_representative(p,q)==r)cases.push_back({i,j});
  }
  int first=0,last=cases.size();
  if(argc>5){first=atoi(argv[5]);last=first+1;
   if(first<0||first>=(int)cases.size()){cerr<<"Invalid diameter case index\n";return 2;}}
  string scope=(argc>5?(top2?string(argv[4])+"_diameter_case":"diameter_case"):(top2?string("all_")+argv[4]+"_diameter_cases":"all_diameter_cases"));
  cerr<<"diameter threshold "<<threshold<<" cases "<<cases.size()<<" selected "<<first<<".."<<last-1<<"\n";
  for(int ci=first;ci<last;ci++){
   int p=cases[ci].first,q=cases[ci].second;
   max_distance=dist[p][q];
   vector<Candidate>c;
   for(int j=0;j<N;j++)if(j!=p&&j!=q&&dist[j][p]<max_distance&&dist[j][q]<max_distance&&dist[j][p]!=dist[j][q]){
    Candidate v;v.v=j;v.radial.set(dist[j][p]);v.radial.set(dist[j][q]);c.push_back(v);
   }
   Mask used;used.set(max_distance);vector<int>chosen{p,q};
   bool found=top2?search_top_two(c,distance_values,p,q,prefix_length):search_diameter(c,used,chosen);
   cerr<<"diameter_case "<<ci<<" squared_distance "<<dist[p][q]<<" endpoints "<<p<<","<<q
       <<" result "<<(found?"SAT":timeout?"UNKNOWN":"UNSAT")<<" nodes "<<nodes<<" seconds "<<elapsed()<<"\n";
   if(found){print_witness(scope,ci);return 0;}
   if(timeout){cout<<"{\"n\":"<<n<<",\"target\":"<<target<<",\"status\":\"UNKNOWN\",\"scope\":\""<<scope<<"\",\"case_index\":"<<ci<<",\"nodes\":"<<nodes<<",\"seconds\":"<<elapsed()<<"}\n";return 3;}
  }
  cout<<"{\"n\":"<<n<<",\"target\":"<<target<<",\"status\":\"UNSAT\",\"scope\":\""<<scope<<"\",\"first_case\":"<<first<<",\"last_case\":"<<last-1<<",\"case_count\":"<<cases.size()<<",\"nodes\":"<<nodes<<",\"seconds\":"<<elapsed()<<"}\n";return 0;
 }
 vector<int>anchors;
 for(int i=0;i<N;i++)if(pts[i][0]==0&&representative(pts[i])==pts[i])anchors.push_back(i);
 int amin=0,amax=anchors.size();
 if(argc>4){amin=atoi(argv[4]);amax=amin+1;
  if(amin<0||amin>=(int)anchors.size()){cerr<<"Invalid anchor index\n";return 2;}}
 string scope=(argc>4?"anchor_case":"all_anchor_cases");
 for(int a=amin;a<amax;a++){
  int p=anchors[a];
  vector<Candidate>c;
  // For the lexicographically least image under translations and cube
  // symmetries, the first point is a chamber point with x=0.  Furthermore
  // no selected point can have a lexicographically smaller orbit image.
  for(int j=p+1;j<N;j++)if(representative(pts[j])>=pts[p]){
   Candidate q;q.v=j;q.radial.set(dist[p][j]);c.push_back(q);
  }
  vector<int>chosen{p};Mask used;
  bool found=search(c,used,chosen,all_occupancies);
  cerr<<"anchor "<<a<<" point "<<pts[p][0]<<","<<pts[p][1]<<","<<pts[p][2]
      <<" result "<<(found?"SAT":timeout?"UNKNOWN":"UNSAT")
      <<" nodes "<<nodes<<" seconds "<<elapsed()<<"\n";
  if(found){
   print_witness(scope,a);return 0;
  }
  if(timeout){cout<<"{\"n\":"<<n<<",\"target\":"<<target<<",\"status\":\"UNKNOWN\",\"scope\":\""<<scope<<"\",\"case_index\":"<<a<<",\"nodes\":"<<nodes<<",\"seconds\":"<<elapsed()<<"}\n";return 3;}
 }
 cout<<"{\"n\":"<<n<<",\"target\":"<<target<<",\"status\":\"UNSAT\",\"scope\":\""<<scope<<"\",\"first_case\":"<<amin<<",\"last_case\":"<<amax-1<<",\"case_count\":"<<anchors.size()<<",\"nodes\":"<<nodes<<",\"seconds\":"<<elapsed()<<"}\n";
}
