#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <unordered_map>
#include <vector>
using namespace std;
using BS=array<uint64_t,8>;
struct T{int typ,a,b;array<int,6>v;};
static uint64_t key(int a,int b){return(uint64_t(uint32_t(a))<<32)|uint32_t(b);}
int main(int argc,char**argv){
 ifstream f(argv[1]);int N,M,rt;f>>N>>M>>rt;if(N>512)return 2;
 vector<pair<int,int>> nodes(N);unordered_map<uint64_t,int> initial;
 vector<BS>reach(N);for(int i=0;i<N;++i){f>>nodes[i].first>>nodes[i].second;reach[i][i>>6]|=uint64_t(1)<<(i&63);if(nodes[i].first>=0){initial[key(nodes[i].first,nodes[i].second)]=i;for(int w=0;w<8;++w)reach[i][w]|=reach[nodes[i].first][w]|reach[nodes[i].second][w];}}
 vector<T> ts(M);BS fixed{};array<array<BS,6>,8> rr{};
 for(auto&t:ts){f>>t.typ;if(t.typ==0){f>>t.a;for(int w=0;w<8;++w)fixed[w]|=reach[t.a][w];}else if(t.typ==1){f>>t.a;for(int k=0;k<6;++k){f>>t.v[k];for(int w=0;w<8;++w)rr[t.a][k][w]|=reach[t.v[k]][w];}}else f>>t.a>>t.b;}
 long hist[512]{};int best=1000;array<int,8>c{};vector<int>v(M);vector<pair<int,int>>fresh;fresh.reserve(M);
 for(int ci=0;ci<1679616;++ci){int x=ci;for(int i=0;i<8;++i){c[i]=x%6;x/=6;}BS live=fixed;for(int i=0;i<8;++i)for(int w=0;w<8;++w)live[w]|=rr[i][c[i]][w];int count=0;fresh.clear();
  for(int i=0;i<M;++i){auto&t=ts[i];if(t.typ==0)v[i]=t.a;else if(t.typ==1)v[i]=t.v[c[t.a]];else{int a=v[t.a],b=v[t.b],id=-1;if(a<N&&b<N){auto it=initial.find(key(a,b));if(it!=initial.end())id=it->second;}if(id<0){for(int j=0;j<(int)fresh.size();++j)if(fresh[j].first==a&&fresh[j].second==b){id=N+j;break;}if(id<0){id=N+fresh.size();fresh.push_back({a,b});}}v[i]=id;if(id<N)live[id>>6]|=uint64_t(1)<<(id&63);}}
  for(auto w:live)count+=popcount(w);count+=fresh.size();hist[count]++;
  if(count<=best){if(count<best){best=count;cerr<<"best "<<best<<" choice";for(auto k:c)cerr<<' '<<k;cerr<<'\n';}if(count<=205){cout<<count;for(auto k:c)cout<<' '<<k;cout<<'\n';}}
 }
 cerr<<"DONE best "<<best<<"\n";for(int k=0;k<512;++k)if(hist[k])cerr<<k<<' '<<hist[k]<<'\n';
}
