#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <vector>
using namespace std;
using Key=array<long long,5>;
map<Key,long long> found;
long long qcounts[8]={}, corecounts[8]={}, markcounts[8]={};
vector<int> bits[128];
void inspect(const vector<unsigned>&q,const vector<int>&sz){
 vector<int> cl;for(int i=0;i<(int)sz.size();i++)for(int j=0;j<sz[i];j++)cl.push_back(i);
 int n=cl.size(),L=1<<n;vector<unsigned>rows(n);vector<int>mins;
 for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(i!=j&&(cl[i]==cl[j]||(q[cl[i]]&(1u<<cl[j]))))rows[i]|=1u<<j;
 for(int v=0;v<n;v++){bool yes=true;for(int i=0;i<n;i++)if(rows[i]&(1u<<v))yes=false;if(yes)mins.push_back(v);}
 corecounts[n]++;if(mins.empty())return;
 static uint8_t possible[128][128];fill(&possible[0][0],&possible[0][0]+16384,0);possible[0][0]=1;
 long long p[4]={1,0,0,0};long long del[7][4]={};
 for(int k=1;k<=n/2;k++)for(int A=1;A<L;A++)if(__builtin_popcount((unsigned)A)==k){int i=bits[A][0];for(int B=1;B<L;B++)if(!(A&B)&&__builtin_popcount((unsigned)B)==k){
  bool ok=false;for(int j:bits[B])if((rows[i]&(1u<<j))&&possible[A^(1<<i)][B^(1<<j)]){ok=true;break;}
  possible[A][B]=ok;if(ok){p[k]++;for(int v:mins)if(!((A|B)&(1<<v)))del[v][k]++;}
 }}
 for(int v:mins)if(del[v][3]==0){found[{p[1],p[2],p[3],del[v][1],del[v][2]}]++;markcounts[n]++;}
}
void compositions(const vector<unsigned>&q,vector<int>&sz,int at,int left){if(at==(int)sz.size()-1){sz[at]=left;inspect(q,sz);return;}for(int a=1;a<=left-((int)sz.size()-at-1);a++){sz[at]=a;compositions(q,sz,at+1,left-a);}}
void visit(const vector<unsigned>&q){int k=q.size();if(k){qcounts[k]++;for(int n=k;n<=7;n++){vector<int>sz(k);compositions(q,sz,0,n);}}if(k==7)return;
 // The predecessors of the newly appended maximal point form an order ideal.
 for(unsigned S=0;S<(1u<<k);S++){bool ideal=true;for(int j=0;j<k;j++)if(S&(1u<<j))for(int i=0;i<k;i++)if((q[i]&(1u<<j))&&!(S&(1u<<i)))ideal=false;if(!ideal)continue;vector<unsigned>nq=q;for(int i=0;i<k;i++)if(S&(1u<<i))nq[i]|=1u<<k;nq.push_back(0);visit(nq);}
}
int main(){for(int A=0;A<128;A++)for(int i=0;i<7;i++)if(A&(1<<i))bits[A].push_back(i);visit({});for(auto const &[k,c]:found){for(auto v:k)cout<<v<<',';cout<<c<<'\n';}for(int n=1;n<=7;n++)cerr<<n<<' '<<qcounts[n]<<' '<<corecounts[n]<<' '<<markcounts[n]<<'\n';}
