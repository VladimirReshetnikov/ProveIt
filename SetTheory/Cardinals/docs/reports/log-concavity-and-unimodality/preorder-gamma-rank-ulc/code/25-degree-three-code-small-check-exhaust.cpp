// Exact exhaustive finite preorder check, n<=8.
// Quotient posets are naturally labeled; positive block sizes cover all preorders
// up to relabeling, with intentional repetitions. All mathematical arithmetic integral.
#include <bits/stdc++.h>
using namespace std;
using ll=long long;
struct Pair {unsigned a,b; int k;};
struct Witness {vector<unsigned> rows; vector<int> blocks; unsigned qmask=0; array<ll,4> g{};};
struct Stats {ll cases=0,degree4=0,degree3=0,nonbip3=0,bad1=0,bad2=0,baddisc=0; ll mingap=LLONG_MAX,mindisc=LLONG_MAX; ll ratnum=LLONG_MAX,ratden=1; Witness wg,wd,wr;};
vector<Pair> pairs; unsigned rows[8]; int n,m; unsigned qmask; vector<unsigned> qrows; vector<int> blocks; vector<Stats> stats(9); map<array<ll,4>,pair<ll,ll>> hist[9]; map<array<ll,4>, Witness> representatives[9]; ll qcounts[9]={}, expansions[9][9]={};
bool match(unsigned a,unsigned b){if(!a)return true; int i=__builtin_ctz(a); unsigned avail=rows[i]&b; a&=a-1; while(avail){unsigned bit=avail&-avail;avail-=bit;if(match(a,b^bit))return true;}return false;}
bool bipartite(){int color[8];fill(color,color+8,-1);for(int s=0;s<n;s++)if(color[s]<0){color[s]=0; vector<int> q={s};for(size_t h=0;h<q.size();h++){int v=q[h];for(int w=0;w<n;w++)if((rows[v]>>w&1)||(rows[w]>>v&1)){if(color[w]<0){color[w]=color[v]^1;q.push_back(w);}else if(color[w]==color[v])return false;}}}return true;}
Witness witness(array<ll,4> g){return {vector<unsigned>(rows,rows+n),blocks,qmask,g};}
bool undirected_perfect(unsigned v){if(!v)return true; int i=__builtin_ctz(v);v&=v-1;for(unsigned cand=v;cand;cand&=cand-1){int j=__builtin_ctz(cand);if(((rows[i]>>j&1)||(rows[j]>>i&1))&&undirected_perfect(v^(1u<<j)))return true;}return false;}
void evaluate(){int cls[8],p=0;for(int i=0;i<m;i++)for(int j=0;j<blocks[i];j++)cls[p++]=i;
 fill(rows,rows+8,0);for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(i!=j &&(cls[i]==cls[j]||(qrows[cls[i]]>>cls[j]&1)))rows[i]|=1u<<j;
 auto &s=stats[n];s.cases++;expansions[n][m]++;
 if(n==8&&undirected_perfect((1u<<n)-1)){s.degree4++;return;}
 array<ll,4>g={1,0,0,0};for(auto p:pairs)if(match(p.a,p.b))g[p.k]++;
 bool nb=!bipartite();if(!hist[n].count(g)) representatives[n][g]=witness(g);hist[n][g].first++;hist[n][g].second+=nb;
 if(!g[3]) return;
 s.degree3++;s.nonbip3+=nb;
 ll a=g[1],b=g[2],c=g[3],gap1=a*a-3*b,gap=b*b-3*a*c;
 ll disc=a*a*b*b-4*b*b*b-4*a*a*a*c-27*c*c+18*a*b*c;
 s.bad1+=gap1<0;s.bad2+=gap<0;s.baddisc+=disc<0;
 if(gap<s.mingap){s.mingap=gap;s.wg=witness(g);}if(disc<s.mindisc){s.mindisc=disc;s.wd=witness(g);}
 if(s.ratnum==LLONG_MAX || b*b*s.ratden<s.ratnum*(3*a*c)){s.ratnum=b*b;s.ratden=3*a*c;s.wr=witness(g);}
}
void compose(int idx,int left){if(idx==m-1){blocks[idx]=left; evaluate();return;}for(int x=1;x<=left-(m-idx-1);x++){blocks[idx]=x;compose(idx+1,left-x);}}
void print_w(const char* kind,int N,const Witness&w,ll value){cout<<kind<<" n="<<N<<" value="<<value<<" gamma=";for(auto v:w.g)cout<<v<<",";cout<<" blocks=";for(auto b:w.blocks)cout<<b<<",";cout<<" qmask="<<w.qmask<<" rowmasks=";for(auto r:w.rows)cout<<r<<",";cout<<"\n";}
int main(int argc,char**argv){string out=argc>1?argv[1]:".";vector<vector<Pair>> pp(9);for(int N=1;N<=8;N++)for(unsigned a=1;a<(1u<<N);a++){int k=__builtin_popcount(a);if(k>3)continue;for(unsigned b=1;b<(1u<<N);b++)if(!(a&b)&&__builtin_popcount(b)==k)pp[N].push_back({a,b,k});}
 for(m=1;m<=8;m++){
 function<void(vector<unsigned>)> generate=[&](vector<unsigned> r){
 int z=r.size();
 if(z==m){qrows=r;qmask=0;int e=0;for(int i=0;i<m;i++)for(int j=i+1;j<m;j++,e++)if(r[i]>>j&1)qmask|=1u<<e;qcounts[m]++;
 for(n=m;n<=8;n++){pairs=pp[n];blocks.assign(m,0);compose(0,n);}return;}
 for(unsigned pred=0;pred<(1u<<z);pred++){
 bool ideal=true;for(int i=0;i<z;i++)if(!(pred>>i&1)&&(r[i]&pred)){ideal=false;break;}if(!ideal)continue;
 vector<unsigned> nr=r;for(int i=0;i<z;i++)if(pred>>i&1)nr[i]|=1u<<z;nr.push_back(0);generate(nr);
 }
 };generate({});
 cerr<<"quotient_m="<<m<<" naturally_labeled_posets="<<qcounts[m]<<" done\n";
 }
 ofstream wf(out+"/gamma_representatives.csv"); wf<<"n,g0,g1,g2,g3,rowmasks\n";
 for(int N=1;N<=8;N++)for(auto &[g,w]:representatives[N]){wf<<N;for(auto a:g)wf<<","<<a;wf<<",\"";for(size_t j=0;j<w.rows.size();j++){if(j)wf<<" ";wf<<w.rows[j];}wf<<"\"\n";}
 ofstream hf(out+"/gamma_histogram.csv");hf<<"n,g0,g1,g2,g3,enumerated_cases,nonbipartite_cases\n";
 for(n=1;n<=8;n++){auto&s=stats[n];cout<<"n="<<n<<" cases="<<s.cases<<" degree4_skipped="<<s.degree4<<" unique_gamma="<<hist[n].size()<<" degree3="<<s.degree3<<" nonbipartite_degree3="<<s.nonbip3<<" first_gap_failures="<<s.bad1<<" second_gap_failures="<<s.bad2<<" discriminant_negative="<<s.baddisc<<"\n";
 for(auto&[g,c]:hist[n]){hf<<n;for(auto a:g)hf<<","<<a;hf<<","<<c.first<<","<<c.second<<"\n";}
 if(s.degree3){print_w("minimum_second_gap",n,s.wg,s.mingap);print_w("minimum_discriminant",n,s.wd,s.mindisc);ll d=gcd(s.ratnum,s.ratden);cout<<"minimum_second_ratio n="<<n<<" fraction="<<s.ratnum/d<<"/"<<s.ratden/d<<"\n";print_w("minimum_second_ratio_witness",n,s.wr,0);}}
 cout<<"quotient_counts";for(m=1;m<=8;m++)cout<<","<<qcounts[m];cout<<"\n";for(n=1;n<=8;n++){cout<<"expansions_by_quotient_size n="<<n;for(m=1;m<=n;m++)cout<<","<<expansions[n][m];cout<<"\n";}
}
