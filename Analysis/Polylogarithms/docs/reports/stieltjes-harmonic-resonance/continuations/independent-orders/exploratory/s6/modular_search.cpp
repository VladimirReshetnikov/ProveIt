// Exploratory finite-field elimination. This program is NOT an identity proof.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <queue>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using I=int64_t; const I P=2147483647;
using Row=std::unordered_map<int,I>;
I powm(I a,I n){I s=1;for(;n;n>>=1,a=a*a%P)if(n&1)s=s*a%P;return s;}
struct Step{int old,pivot;I coefficient;};
int main(int argc,char**argv){
 if(argc<2)return 2;int limit=argc>2?std::stoi(argv[2]):240;
 std::ifstream f(argv[1]);int n,nc;f>>n>>nc;int target=n-1;
 std::vector<Row> rows(n);std::vector<std::unordered_set<int>> cols(nc);
 size_t nnz=0;for(int i=0;i<n;i++){int k;f>>k;rows[i].reserve(k*2+1);nnz+=k;
  for(int t=0;t<k;t++){int c;I a;f>>c>>a;a%=P;if(a<0)a+=P;rows[i][c]=a;cols[c].insert(i);}}
 using Pair=std::pair<size_t,int>;
 std::priority_queue<Pair,std::vector<Pair>,std::greater<Pair>> heap;
 for(int i=0;i<target;i++)if(!rows[i].empty())heap.push({rows[i].size(),i});
 std::vector<bool> active(n,true);std::vector<int> node(n);for(int i=0;i<n;i++)node[i]=i;
 std::vector<Step> steps;steps.reserve(1000000);
 auto start=std::chrono::steady_clock::now();int rank=0;
 auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 std::cerr<<"rows "<<n<<" entries "<<nnz<<" modulus "<<P<<"\n";
 while(!rows[target].empty()&&!heap.empty()){
  auto [sz,i]=heap.top();heap.pop();if(!active[i]||rows[i].size()!=sz)continue;
  if(rank%100==0&&elapsed()>limit)break;
  int c=-1;size_t best=std::numeric_limits<size_t>::max();
  for(auto [h,a]:rows[i])if(cols[h].size()<best||(cols[h].size()==best&&h<c)){best=cols[h].size();c=h;}
  if(c<0)continue;auto &pivot=rows[i];I inv=powm(pivot[c],P-2);int pn=node[i];
  std::vector<int> affected(cols[c].begin(),cols[c].end());std::sort(affected.begin(),affected.end());
  for(int k:affected){if(k==i)continue;auto &row=rows[k];I a=row[c]*inv%P;nnz-=row.size();
   for(auto [h,b]:pivot){I value=b*a%P;auto it=row.find(h);
    if(it==row.end()){row[h]=P-value;cols[h].insert(k);}else{I v=it->second-value;if(v<0)v+=P;
     if(v){it->second=v;}else{row.erase(it);cols[h].erase(k);}}}
   steps.push_back({node[k],pn,a});node[k]=n+steps.size()-1;nnz+=row.size();
   if(k!=target&&!row.empty())heap.push({row.size(),k});}
  nnz-=pivot.size();for(auto [h,a]:pivot)cols[h].erase(i);Row().swap(pivot);active[i]=false;rank++;
  if(rank%500==0)std::cerr<<"pivots "<<rank<<" seconds "<<elapsed()<<" entries "<<nnz<<" target "<<rows[target].size()<<" nodes "<<steps.size()<<"\n";
 }
 std::cout<<"{\"modulus\":"<<P<<",\"pivots\":"<<rank<<",\"elapsed_seconds\":"<<elapsed()<<",\"remaining_entries\":"<<nnz<<",\"target_terms\":"<<rows[target].size()<<",\"dag_nodes\":"<<steps.size()<<",\"target_zero_mod_prime\":"<<(rows[target].empty()?"true":"false")<<",\"row_span_exhausted\":"<<(heap.empty()?"true":"false")<<"}\n";
 if(rows[target].empty()){
  std::vector<I> weights(n+steps.size());weights[node[target]]=1;
  for(int j=(int)steps.size()-1;j>=0;j--){I x=weights[n+j];if(!x)continue;auto [old,piv,a]=steps[j];weights[old]=(weights[old]+x)%P;I b=x*a%P;weights[piv]=(weights[piv]+P-b)%P;}
  std::ofstream out(std::string(argv[1])+".modular_coefficients");for(int j=0;j<target;j++)if(weights[j])out<<j<<' '<<(P-weights[j])<<'\n';
 }
}
