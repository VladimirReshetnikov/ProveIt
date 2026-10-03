// Independent exhaustive recount: reuse only the audited literal-matrix
// canonicalizer; independently generate ideals, positive block weights,
// matching ranks, and support counts. Hall tests replace matching recursion.
#include <bits/stdc++.h>
namespace canonical_source {
#define main production_main
#include "/workspace/shared/preorder-gamma-degree4/exhaust10_canonical.cpp"
#undef main
}
using namespace std;
using Key=__uint128_t; using ll=long long;
constexpr unsigned FULL=1023;
unsigned rel[10], und[10], nbr[1024]; unsigned char pop[1024];
signed char memo[1024];
int rank_of(unsigned mask){
  if(!mask)return 0;
  if(memo[mask]>=0)return memo[mask];
  int v=__builtin_ctz(mask);unsigned tail=mask&(mask-1);
  int bound=pop[mask]/2,best=0;
  for(unsigned js=und[v]&tail;js;js&=js-1){
    best=max(best,1+rank_of(tail^(js&-js)));
    if(best==bound)return memo[mask]=best;
  }
  best=max(best,rank_of(tail)); return memo[mask]=best;
}
struct Candidate{unsigned a,b;int k;};
vector<Candidate> candidates;
vector<unsigned> subsets[1024];
ll cases=0, degree4=0, marked=0, neglinear=0;
ll min_gap[3]={LLONG_MAX,LLONG_MAX,LLONG_MAX};
set<array<ll,9>> families;
ll pair_fail=0;
void check_relation(const vector<unsigned>&q,const vector<int>&sizes){
  int cls[10],p=0;
  for(int i=0;i<(int)q.size();i++)for(int j=0;j<sizes[i];j++)cls[p++]=i;
  assert(p==10);fill(rel,rel+10,0);fill(und,und+10,0);
  for(int i=0;i<10;i++)for(int j=0;j<10;j++)if(i!=j){
    if(cls[i]==cls[j] || (q[cls[i]]&(1u<<cls[j])))rel[i]|=1u<<j;
  }
  for(int i=0;i<10;i++)for(int j=0;j<10;j++)if((rel[i]&(1u<<j))||(rel[j]&(1u<<i)))und[i]|=1u<<j;
  cases++; fill(memo,memo+1024,-1);
  int rank=rank_of(FULL);
  unsigned marked_vertices=0;
  for(int v=0;v<10;v++){
    bool source=true;
    for(int i=0;i<10;i++)if(rel[i]&(1u<<v))source=false;
    if((source || rel[v]==0) && rank_of(FULL^(1u<<v))==3)marked_vertices|=1u<<v;
  }
  if(rank!=4 && !marked_vertices)return;
  nbr[0]=0;
  for(unsigned s=1;s<1024;s++)nbr[s]=nbr[s&(s-1)]|rel[__builtin_ctz(s)];
  ll g[5]={1,0,0,0,0}, deleted[10][5]={};
  for(int v=0;v<10;v++)deleted[v][0]=1;
  for(const Candidate&s:candidates){
    bool feasible=true;
    for(unsigned t:subsets[s.a])if(pop[nbr[t]&s.b]<pop[t]){feasible=false;break;}
    if(!feasible)continue;
    g[s.k]++;
    for(unsigned vv=marked_vertices&~(s.a|s.b);vv;vv&=vv-1)deleted[__builtin_ctz(vv)][s.k]++;
  }
  assert((g[4]>0)==(rank>=4));
  if(rank==4){
    degree4++;
    ll gaps[3]={3*g[1]*g[1]-8*g[2],4*g[2]*g[2]-9*g[1]*g[3],3*g[3]*g[3]-8*g[2]*g[4]};
    for(int k=0;k<3;k++){assert(gaps[k]>=0);min_gap[k]=min(min_gap[k],gaps[k]);}
  }
  for(unsigned vv=marked_vertices;vv;vv&=vv-1){
    int v=__builtin_ctz(vv);ll*b=deleted[v];
    assert(b[3]>0 && b[4]==0 && rank<=4);
    array<ll,9> pair;
    copy(g,g+5,pair.begin());copy(b,b+4,pair.begin()+5);
    families.insert(pair);marked++;
    // Coefficients recovered by values at M=0,1,2, not hard-coded.
    ll vals[3][3];
    for(int M=0;M<=2;M++){
      ll h[5]={1,0,0,0,0};for(int k=1;k<=4;k++)h[k]=g[k]+M*b[k-1];
      vals[0][M]=3*h[1]*h[1]-8*h[2];
      vals[1][M]=4*h[2]*h[2]-9*h[1]*h[3];
      vals[2][M]=3*h[3]*h[3]-8*h[2]*h[4];
    }
    for(int k=0;k<3;k++){
      ll C=vals[k][0],twiceA=vals[k][2]-2*vals[k][1]+C;
      assert(twiceA%2==0);ll A=twiceA/2,B=vals[k][1]-C-A;
      assert(A>=0&&C>=0);if(B<0){neglinear++;assert((__int128)4*A*C>=(__int128)B*B);}
    }
  }
}
void ternary(unsigned pos,unsigned a,unsigned b){
  if(pos==10){if(pop[a]&&pop[a]==pop[b]&&pop[a]<=4)candidates.push_back({a,b,pop[a]});return;}
  ternary(pos+1,a,b);ternary(pos+1,a|(1u<<pos),b);ternary(pos+1,a,b|(1u<<pos));
}
int main(int argc,char**argv){
  assert(argc==2);
  for(int s=0;s<1024;s++)pop[s]=__builtin_popcount((unsigned)s);
  ternary(0,0,0);assert(candidates.size()==8700);
  for(unsigned a=1;a<1024;a++)if(pop[a]<=4){
    for(unsigned t=a;t;t=(t-1)&a)subsets[a].push_back(t);
    sort(subsets[a].begin(),subsets[a].end(),[](unsigned x,unsigned y){return pop[x]>pop[y];});
  }
  vector<vector<unsigned>> previous(1);
  for(int m=1;m<=10;m++){
    set<Key> seen;
    for(auto&q:previous){
      unsigned n=q.size();
      for(unsigned I=0;I<(1u<<n);I++){
        bool downset=true;
        for(unsigned x=0;x<n;x++)for(unsigned y=0;y<n;y++)
          if((I&(1u<<y))&&(q[x]&(1u<<y))&&!(I&(1u<<x)))downset=false;
        if(!downset)continue;
        auto p=q;p.push_back(0);
        for(unsigned x=0;x<n;x++)if(I&(1u<<x))p[x]|=1u<<n;
        seen.insert(canonical_source::canonical(p));
      }
    }
    vector<vector<unsigned>> current;
    for(Key key:seen){
      vector<unsigned>q(m);
      for(int i=0;i<m;i++)for(int j=0;j<m;j++)if((key>>(m*i+j))&1)q[i]|=1u<<j;
      current.push_back(q);
      // A separator set among the nine gaps gives every positive composition.
      for(unsigned sep=0;sep<512;sep++)if(pop[sep]==m-1){
        vector<int> sizes;int run=1;
        for(int gap=0;gap<9;gap++){if(sep&(1u<<gap)){sizes.push_back(run);run=1;}else run++;}
        sizes.push_back(run);assert((int)sizes.size()==m);
        check_relation(q,sizes);
      }
    }
    previous=move(current);
    cout<<"m="<<m<<" quotients="<<seen.size()<<" cases="<<cases<<" actual_degree_four="<<degree4<<" marked="<<marked<<" distinct_pairs="<<families.size()<<endl;
  }
  ofstream out(argv[1]);out<<"a0,a1,a2,a3,a4,b0,b1,b2,b3\n";
  for(auto&r:families){for(int i=0;i<9;i++){if(i)out<<',';out<<r[i];}out<<'\n';}
  assert(cases==5049656 && degree4==686481 && marked==1231416 && families.size()==412622 && neglinear==727924);
  cout<<"PASS cases="<<cases<<" actual_degree_four="<<degree4<<" marked="<<marked<<" distinct_pairs="<<families.size()<<" negative_linear_instances="<<neglinear<<" min_gaps="<<min_gap[0]<<","<<min_gap[1]<<","<<min_gap[2]<<endl;
}
