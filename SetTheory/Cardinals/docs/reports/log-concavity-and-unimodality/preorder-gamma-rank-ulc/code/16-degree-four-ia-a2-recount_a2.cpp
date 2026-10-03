// Complete independent a=2 audit. Canonical keys alone reuse the audited source.
// Core matching feasibility uses Hall inequalities. One-leaf coefficients count
// endpoint supports by Boolean union, without an inclusion-exclusion formula.
#include <bits/stdc++.h>
using namespace std;
#include "audited_canonical.inc"
using Poly=array<int,50>;using ll=long long;
const array<array<int,3>,10> basis={{{0,0,0},{1,0,0},{0,1,0},{0,0,1},{2,0,0},{0,2,0},{0,0,2},{1,1,0},{1,0,1},{0,1,1}}};
Poly normalize(Poly p){Poly q;for(int j=0;j<10;j++){auto e=basis[j];swap(e[0],e[1]);int i=find(basis.begin(),basis.end(),e)-basis.begin();assert(i<10);for(int k=0;k<5;k++)q[10*k+j]=p[10*k+i];}return min(p,q);}
int paircolumn(int t,int u){array<int,3>e={};e[t-1]++;e[u-1]++;int i=find(basis.begin(),basis.end(),e)-basis.begin();assert(i<10);return i;}
unsigned rel[8],und[8],unions[256];int pop[256],mdp[256];
bool feasible[256][256];
struct Support{unsigned a,b;int k;};vector<Support>balanced,larger;
vector<unsigned>subsets[256];vector<unsigned>small_neighbors;
struct Spec{int a,b,s,L;};
struct Target{int id,L;Poly p;};
map<string,Target>targets;vector<bool>verified;set<Poly>expected,obtained;
string spec_key(int a,int b,int s){string k;for(auto x:rel)k+=char(x);k+=char(a);k+=char(b);k+=char(s);return k;}
ll cores=0,eligible=0,specs=0,degree_four=0,checked=0;
int matching_rank(unsigned mask){if(!mask)return 0;int&v=mdp[mask];if(v>=0)return v;unsigned tail=mask&(mask-1);int i=__builtin_ctz(mask);v=matching_rank(tail);for(unsigned xs=und[i]&tail;xs;xs&=xs-1)v=max(v,1+matching_rank(tail^(xs&-xs)));return v;}
bool extension_is_preorder(int a,int b,int sign,const vector<int>&types){
 vector<unsigned>r(rel,rel+8);r.resize(8+types.size());int n=r.size();
 for(int j=0;j<(int)types.size();j++)for(int h=0;h<2;h++)if(types[j]&(1<<h)){
   int v=h?b:a;if(sign&(1<<h))r[v]|=1u<<(8+j);else r[8+j]|=1u<<v;
 }
 for(int i=0;i<n;i++)r[i]|=1u<<i;
 auto closure=r;
 for(int mid=0;mid<n;mid++)for(int i=0;i<n;i++)if(closure[i]&(1u<<mid))closure[i]|=closure[mid];
 return closure==r;
}
int pairweights[4][4][4];
void compute_pairweights(){
 for(int s=0;s<4;s++)for(int t=1;t<=3;t++)for(int u=1;u<=3;u++){
   unsigned r[4]={};int ts[2]={t,u};
   for(int j=0;j<2;j++)for(int h=0;h<2;h++)if(ts[j]&(1<<h)){
     if(s&(1<<h))r[h]|=1u<<(2+j);else r[2+j]|=1u<<h;
   }
   int w=0;
   for(unsigned A=0;A<16;A++)if(__builtin_popcount(A)==2){
     unsigned B=15^A;bool okay=true;
     for(unsigned S=A;S;S=(S-1)&A){unsigned N=0;for(int i=0;i<4;i++)if(S&(1<<i))N|=r[i];if(__builtin_popcount(N&B)<__builtin_popcount(S))okay=false;}
     if(okay)w++;
   }
   pairweights[s][t][u]=w;
 }
}
void check_core(const vector<unsigned>&q,const vector<int>&sizes){
 cores++;int cls[8],n=0;
 for(int i=0;i<(int)q.size();i++)for(int j=0;j<sizes[i];j++)cls[n++]=i;
 assert(n==8);fill(rel,rel+8,0);fill(und,und+8,0);
 for(int i=0;i<8;i++)for(int j=0;j<8;j++)if(i!=j&&(cls[i]==cls[j]||(q[cls[i]]&(1u<<cls[j]))))rel[i]|=1u<<j;
 for(int i=0;i<8;i++)for(int j=0;j<8;j++)if((rel[i]&(1u<<j))||(rel[j]&(1u<<i)))und[i]|=1u<<j;
 fill(mdp,mdp+256,-1);
 vector<Spec>allowed;
 for(int a=0;a<8;a++)for(int b=a+1;b<8;b++){
   if(matching_rank(255^(1u<<a)^(1u<<b))>2)continue;
   for(int s=0;s<4;s++){
     int legal=0;vector<int>types;
     for(int t=1;t<=3;t++)if(extension_is_preorder(a,b,s,{t,t})){legal|=1<<t;types.push_back(t);}
     if(!legal)continue;
     assert(extension_is_preorder(a,b,s,types));
     allowed.push_back({a,b,s,legal});
   }
 }
 if(allowed.empty())return;eligible++;
 unions[0]=0;for(unsigned x=1;x<256;x++)unions[x]=unions[x&(x-1)]|rel[__builtin_ctz(x)];
 memset(feasible,0,sizeof feasible);int gamma[5]={},deleted_pair[8][8][5]={};
 for(auto p:balanced){
   bool okay=true;for(auto S:subsets[p.a])if(pop[unions[S]&p.b]<pop[S]){okay=false;break;}
   feasible[p.a][p.b]=okay;if(!okay)continue;gamma[p.k]++;
   for(int a=0;a<8;a++)if(!((p.a|p.b)&(1u<<a)))for(int b=a+1;b<8;b++)if(!((p.a|p.b)&(1u<<b)))deleted_pair[a][b][p.k]++;
 }
 // Histogram of which potential partners permit the residual core support.
 int hist[2][5][256]={},one[2][5][256]={};
 for(auto p:larger){
   unsigned to_leaf=0,from_leaf=0;
   for(unsigned vs=p.a;vs;vs&=vs-1){unsigned v=vs&-vs;if(feasible[p.a^v][p.b])to_leaf|=v;if(feasible[p.b][p.a^v])from_leaf|=v;}
   hist[0][p.k][to_leaf]++;hist[1][p.k][from_leaf]++;
 }
 // Direct Boolean union: each fixed support contributes once if ANY possible
 // partner works. In particular there is no subtraction or overlap identity.
 for(int dir=0;dir<2;dir++)for(int k=1;k<=4;k++)for(unsigned N:small_neighbors)
   for(unsigned good=1;good<256;good++)if(good&N)one[dir][k][N]+=hist[dir][k][good];
 for(auto S:allowed){
   specs++;Poly p={};for(int k=0;k<5;k++)p[10*k]=gamma[k];
   for(int t=1;t<=3;t++)if(S.L&(1<<t)){
     unsigned sinkN=0,sourceN=0;for(int h=0;h<2;h++)if(t&(1<<h)){unsigned bit=1u<<(h?S.b:S.a);if(S.s&(1<<h))sinkN|=bit;else sourceN|=bit;}
     for(int k=1;k<=4;k++)p[10*k+t]=one[0][k][sinkN]+one[1][k][sourceN];
   }
   for(int t=1;t<=3;t++)if(S.L&(1<<t))for(int u=t;u<=3;u++)if(S.L&(1<<u)){
     int j=paircolumn(t,u),w=pairweights[S.s][t][u];for(int k=2;k<=4;k++)p[10*k+j]=w*deleted_pair[S.a][S.b][k-2];
   }
   bool degree4=false;for(int j=0;j<10;j++)if(p[40+j])degree4=true;
   if(!degree4)continue;degree_four++;Poly key=normalize(p);obtained.insert(key);
   auto it=targets.find(spec_key(S.a,S.b,S.s));if(it!=targets.end()){
     auto&T=it->second;assert(T.L==S.L);if(T.p!=key){cerr<<"MISMATCH id="<<T.id<<endl;abort();}
     if(!verified[T.id]){verified[T.id]=true;checked++;}
   }
 }
}
void generate_roles(int pos,unsigned a,unsigned b){if(pos==8){int x=pop[a],y=pop[b];if(x==y&&x<=4)balanced.push_back({a,b,x});if(x==y+1&&x<=4)larger.push_back({a,b,x});return;}generate_roles(pos+1,a,b);generate_roles(pos+1,a|(1u<<pos),b);generate_roles(pos+1,a,b|(1u<<pos));}
int main(int argc,char**argv){
 assert(argc==2);for(int i=0;i<256;i++)pop[i]=__builtin_popcount((unsigned)i);
 generate_roles(0,0,0);
 for(unsigned a=1;a<256;a++)if(pop[a]<=4){for(unsigned S=a;S;S=(S-1)&a)subsets[a].push_back(S);sort(subsets[a].begin(),subsets[a].end(),[](unsigned x,unsigned y){return pop[x]>pop[y];});}
 for(unsigned N=1;N<256;N++)if(pop[N]<=2)small_neighbors.push_back(N);
 ifstream in(argv[1]);int id;
 while(in>>id){for(auto&x:rel)in>>x;int a,b,s,L;in>>a>>b>>s>>L;Poly p;for(auto&x:p)in>>x;assert(in);string key=spec_key(a,b,s);assert(!targets.count(key));targets.emplace(key,Target{id,L,p});expected.insert(p);}
 assert(targets.size()==89863&&expected.size()==89863);verified.assign(89863,false);compute_pairweights();
 vector<vector<unsigned>>previous(1);
 for(int m=1;m<=8;m++){
   set<Key>keys;
   for(auto&q:previous){int n=q.size();for(unsigned I=0;I<(1u<<n);I++){
     bool ideal=true;for(int x=0;x<n;x++)for(int y=0;y<n;y++)if((I&(1u<<y))&&(q[x]&(1u<<y))&&!(I&(1u<<x)))ideal=false;
     if(!ideal)continue;auto r=q;r.push_back(0);for(int x=0;x<n;x++)if(I&(1u<<x))r[x]|=1u<<n;keys.insert(canonical(r));
   }}
   vector<vector<unsigned>>current;
   for(Key key:keys){vector<unsigned>q(m);for(int i=0;i<m;i++)for(int j=0;j<m;j++)if((key>>(m*i+j))&1)q[i]|=1u<<j;current.push_back(q);
     for(unsigned sep=0;sep<128;sep++)if(pop[sep]==m-1){vector<int>sizes;int run=1;for(int gap=0;gap<7;gap++){if(sep&(1u<<gap)){sizes.push_back(run);run=1;}else run++;}sizes.push_back(run);check_core(q,sizes);}
   }
   previous=move(current);cout<<"m="<<m<<" quotients="<<keys.size()<<" cores="<<cores<<" eligible="<<eligible<<" specifications="<<specs<<" degree_four_specifications="<<degree_four<<" unique_polynomials="<<obtained.size()<<" representatives_verified="<<checked<<endl;
 }
 assert(cores==40877&&eligible==32236&&specs==802333&&degree_four==667508&&obtained.size()==89863);
 assert(obtained==expected);assert(checked==89863);
 cout<<"PASS: complete polynomial set matches; all 89863 stored representatives exactly verified."<<endl;
}
