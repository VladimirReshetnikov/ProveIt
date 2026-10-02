// Exact gamma and binomial-basis Newton gap polynomials for all retained cover4 templates.
#include<bits/stdc++.h>
using namespace std;using ll=long long;using Code=uint64_t;
unsigned rows[8];struct Support{unsigned a,b;int k;};vector<Support>supports[5];
bool match(unsigned a,unsigned b){if(!a)return true;unsigned opts=rows[__builtin_ctz(a)]&b;a&=a-1;while(opts){unsigned bit=opts&-opts;opts-=bit;if(match(a,b^bit))return true;}return false;}
using Poly=map<Code,ll>;ll fact[]={1,1,2,6,24,120,720,5040,40320};
void binproduct(Poly&A,Poly&B,Poly&C,ll scalar,int d){for(auto[a,u]:A)for(auto[b,v]:B){vector<tuple<int,int,int>>overlap;ll multiplier=scalar*u*v;for(int i=0;i<d;i++){int x=(a>>(3*i))&7,y=(b>>(3*i))&7;if(x&&y)overlap.push_back({i,x,y});}
 function<void(int,Code,ll)>go=[&](int at,Code code,ll weight){if(at==(int)overlap.size()){C[code]+=weight;return;}auto[i,x,y]=overlap[at];for(int j=0;j<=min(x,y);j++){ll f=fact[x+y-j]/(fact[j]*fact[x-j]*fact[y-j]);go(at+1,code-(Code(j)<<(3*i)),weight*f);}};go(0,a+b,multiplier);}}
void print_poly(ostream&f,Poly&p){f<<"[";bool first=true;for(auto[e,c]:p)if(c){if(!first)f<<",";first=false;f<<"["<<e<<","<<c<<"]";}f<<"]";}
int main(int argc,char**argv){string folder=argc>1?argv[1]:".";ifstream in(folder+"/templates.tsv");ofstream gf(folder+"/a4_polynomials.jsonl"),pf(folder+"/a4_gaps.jsonl");
 for(int extra=0;extra<=4;extra++){int N=4+extra;unsigned mandatory=((1u<<extra)-1)<<4;for(unsigned a=0;a<(1u<<N);a++){int k=__builtin_popcount(a);if(k>4||k<extra)continue;unsigned comp=((1u<<N)-1)^a;for(unsigned b=comp;;b=(b-1)&comp){if(__builtin_popcount(b)==k&&((a|b)&mandatory)==mandatory)supports[extra].push_back({a,b,k});if(!b)break;}}}
 int id,s,d;vector<unsigned>core(4);while(in>>id>>core[0]>>core[1]>>core[2]>>core[3]>>s>>d){vector<int>ts(d);for(int&t:ts)in>>t;vector<vector<int>>Q;vector<array<ll,5>>G;vector<int>q(d);array<Poly,5>gp;
 function<void(int,int)>go=[&](int i,int left){if(i<d){for(int k=0;k<=left;k++){q[i]=k;go(i+1,left-k);}return;}vector<int>ext;Code code=0;for(int j=0;j<d;j++){code|=Code(q[j])<<(3*j);for(int k=0;k<q[j];k++)ext.push_back(ts[j]);}fill(rows,rows+8,0);copy(core.begin(),core.end(),rows);for(int j=0;j<(int)ext.size();j++)for(int a=0;a<4;a++)if(ext[j]>>a&1){if(s>>a&1)rows[a]|=1u<<(4+j);else rows[4+j]|=1u<<a;}array<ll,5>g={};for(auto p:supports[ext.size()])if(match(p.a,p.b))g[p.k]++;Q.push_back(q);G.push_back(g);for(int k=0;k<5;k++)if(g[k])gp[k][code]=g[k];};go(0,4);
 gf<<"{\"id\":"<<id<<",\"core_rows\":[";for(int i=0;i<4;i++){if(i)gf<<",";gf<<core[i];}gf<<"],\"orientation_mask\":"<<s<<",\"types\":[";for(int i=0;i<d;i++){if(i)gf<<",";gf<<ts[i];}gf<<"],\"quota\":[";for(int i=0;i<(int)Q.size();i++){if(i)gf<<",";gf<<"[";for(int j=0;j<d;j++){if(j)gf<<",";gf<<Q[i][j];}gf<<"]";}gf<<"],\"gamma\":[";for(int k=0;k<5;k++){if(k)gf<<",";gf<<"[";for(int j=0;j<(int)G.size();j++){if(j)gf<<",";gf<<G[j][k];}gf<<"]";}gf<<"]}\n";gf.flush();
 Poly gap2,gap3;binproduct(gp[2],gp[2],gap2,4,d);binproduct(gp[1],gp[3],gap2,-9,d);binproduct(gp[3],gp[3],gap3,3,d);binproduct(gp[2],gp[4],gap3,-8,d);int neg2=0,neg3=0;for(auto[e,c]:gap2)neg2+=c<0;for(auto[e,c]:gap3)neg3+=c<0;
 pf<<"{\"id\":"<<id<<",\"variables\":"<<d<<",\"gap2\":";print_poly(pf,gap2);pf<<",\"gap3\":";print_poly(pf,gap3);pf<<"}\n";pf.flush();cout<<"id="<<id<<" variables="<<d<<" gamma_terms="<<gp[1].size()<<","<<gp[2].size()<<","<<gp[3].size()<<","<<gp[4].size()<<" negative_binomial_coefficients="<<neg2<<","<<neg3<<endl;
 }
 cout<<"COMPLETE"<<endl;
}
