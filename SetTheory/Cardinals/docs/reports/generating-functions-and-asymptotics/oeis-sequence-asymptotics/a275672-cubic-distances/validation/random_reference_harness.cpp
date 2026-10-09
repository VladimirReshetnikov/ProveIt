// Independent branch-and-enumerate comparison for the selected C++ solver.
// The included source is unchanged. Ordinary CLI tests compile it separately.
#define main archived_main
#include "solver_under_audit.cpp"
#undef main
#include <random>
#include <stdexcept>

static bool straightforward_reference(const vector<int>& candidates, int from,
                                     vector<int>& selected, set<int> distances) {
 if ((int)selected.size() == target) return true;
 int need = target - (int)selected.size();
 if ((int)candidates.size() - from < need) return false;
 for (int i = from; i + need <= (int)candidates.size(); ++i) {
  int v = candidates[i];
  set<int> expanded = distances;
  bool good = true;
  for (int a : selected) {
   int d = dist[a][v];
   if (d > max_distance || !expanded.insert(d).second) { good = false; break; }
  }
  if (!good) continue;
  selected.push_back(v);
  if (straightforward_reference(candidates, i + 1, selected, expanded)) {
   selected.pop_back();
   return true;
  }
  selected.pop_back();
 }
 return false;
}

int main() {
 mt19937 rng(20261008);
 int verified = 0, sat = 0, unsat = 0;
 for (int side : {4, 5}) {
  n = side;
  pts.clear(); point_class.clear();
  for (int x = 0; x < n; ++x)
   for (int y = 0; y < n; ++y)
    for (int z = 0; z < n; ++z) pts.push_back({x,y,z});
  N = (int)pts.size();
  dist.assign(N, vector<int>(N));
  array<int,4> capacity{};
  set<int> whole_palette;
  for (auto p : pts) point_class.push_back((p[0]%2)*4+(p[1]%2)*2+p[2]%2);
  for (int i = 0; i < N; ++i) for (int j = 0; j < i; ++j) {
   for (int axis = 0; axis < 3; ++axis) {
    int d = pts[i][axis]-pts[j][axis]; dist[i][j] += d*d;
   }
   dist[j][i] = dist[i][j]; whole_palette.insert(dist[i][j]);
  }
  for (int d : whole_palette) ++capacity[d%4];
  for (int trial = 0; trial < 250; ++trial) {
   vector<int> permutation(N); iota(permutation.begin(),permutation.end(),0);
   shuffle(permutation.begin(),permutation.end(),rng);
   vector<int> selected;
   set<int> prior_distances;
   int selected_size = trial % 4;
   for (int v : permutation) {
    if ((int)selected.size() == selected_size) break;
    set<int> expanded = prior_distances; bool good = true;
    for (int a : selected) if (!expanded.insert(dist[a][v]).second) {good=false;break;}
    if (good) { selected.push_back(v); prior_distances=expanded; }
   }
   target = (int)selected.size() + 1 + rng()%5;
   max_distance = (trial%3 == 0) ? 3*(n-1)*(n-1) : 1+rng()%(3*(n-1)*(n-1));
   vector<Candidate> candidates;
   vector<int> reference_candidates;
   for (int v : permutation) {
    if (find(selected.begin(),selected.end(),v)!=selected.end()) continue;
    set<int> expanded = prior_distances; bool good = true; Candidate c;c.v=v;
    for (int a : selected) {
     int d=dist[a][v];
     if (d>max_distance || !expanded.insert(d).second) {good=false;break;}
     c.radial.set(d);
    }
    if (good) { candidates.push_back(c); reference_candidates.push_back(v); }
    if ((int)candidates.size()==18) break;
   }
   Mask used; for (int d : prior_distances) used.set(d);
   occupancies.clear(); all_occupancies.clear(); array<int,8> counts{};
   generate_occupancies(counts,0,target,capacity);
   auto reference_selected=selected;
   bool expected=straightforward_reference(reference_candidates,0,reference_selected,prior_distances);
   nodes=0; timeout=false; limit=1000; start=Clock::now(); solution.clear();
   bool actual=search(candidates,used,selected,all_occupancies);
   if (timeout || actual!=expected) {
    cerr << "MISMATCH n="<<n<<" trial="<<trial<<" expected="<<expected<<" actual="<<actual<<"\n";
    return 1;
   }
   if (actual) {
    if ((int)solution.size()!=target) throw runtime_error("wrong witness size");
    set<int> witness_distances;
    for(int i=0;i<target;++i)for(int j=0;j<i;++j)
     if(!witness_distances.insert(dist[solution[i]][solution[j]]).second)
      throw runtime_error("repeated witness distance");
    ++sat;
   } else ++unsat;
   ++verified;
  }
 }
 cout << "{\"random_induced_instances\":"<<verified<<",\"sat\":"<<sat<<",\"unsat\":"<<unsat<<",\"status\":\"MATCH\"}\n";
}
