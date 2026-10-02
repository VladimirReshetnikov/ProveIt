// Independent exact, support-based verification of the full balanced monomer identity.
// No producer code or polynomial kernels are imported. Every feasible endpoint support
// is counted once using Hall's condition, then compared coefficientwise with the
// two-copy contraction formula and physical-copy merge, including role activities.
#include <bits/stdc++.h>
using namespace std; using U=unsigned; using I=long long; using Poly=map<U,I>;
int pc(U a){return __builtin_popcount(a);} int lo(U a){return __builtin_ctz(a);}
struct Support{U a,b;int k;}; vector<Support> supports[9]; vector<U> subsets[256];
void enumerate_roles(int n,int i,U a,U b){if(i==n){if(pc(a)==pc(b))supports[n].push_back({a,b,pc(a)});return;} enumerate_roles(n,i+1,a,b);enumerate_roles(n,i+1,a|(1u<<i),b);enumerate_roles(n,i+1,a,b|(1u<<i));}
void clean(Poly&p){for(auto it=p.begin();it!=p.end();)if(!it->second)it=p.erase(it);else ++it;}
Poly mul(const Poly&a,const Poly&b){Poly p;for(auto[x,c]:a)for(auto[y,d]:b){assert(!(x&y));p[x|y]+=c*d;}clean(p);return p;}
void add(Poly&a,const Poly&b,I c){for(auto[x,v]:b)a[x]+=c*v;clean(a);}
vector<int> ts; long cases=0, identities=0,supports_checked=0;
void check(){int e=ts.size(),n=4+e;U rows[8]={3,3,0,0};rows[0]=rows[1]=0;rows[2]=rows[3]=3;for(int i=0;i<e;i++)for(int a=0;a<4;a++)if(ts[i]>>a&1){if(a<2)rows[4+i]|=1u<<a;else rows[a]|=1u<<(4+i);} U neigh[256]={};for(U a=1;a<(1u<<n);a++)neigh[a]=neigh[a&(a-1)]|rows[lo(a)];
 vector<Support> feasible;for(auto s:supports[n]){bool ok=true;for(U a:subsets[s.a])if(pc(neigh[a]&s.b)<pc(a)){ok=false;break;}if(ok)feasible.push_back(s);}supports_checked+=feasible.size();
 Poly h[2],l[2],z[2];for(int side=0;side<2;side++){int shift=side?0:2;U copies=((1u<<e)-1)<<(4+side*e),cores=3u<<shift;h[side][copies|cores]=1;for(int a=0;a<2;a++)l[side][copies|(1u<<(shift+a))]++;
 for(int i=0;i<e;i++){int t=(ts[i]>>shift)&3;U missing=copies^(1u<<(4+side*e+i));for(int a=0;a<2;a++)if(t>>a&1)h[side][missing|(1u<<(shift+1-a))]--;if(t)l[side][missing]--;}
 for(int i=0;i<e;i++)for(int j=i+1;j<e;j++){int a=(ts[i]>>shift)&3,b=(ts[j]>>shift)&3;if(a&&b&&(a|b)==3)h[side][copies^(1u<<(4+side*e+i))^(1u<<(4+side*e+j))]++;}
 z[side][copies]=1;}
 Poly copy=mul(h[0],h[1]);add(copy,mul(l[0],l[1]),-1);add(copy,mul(z[0],z[1]),1);
 for(int variant=0;variant<3;variant++){I w[12];for(int i=0;i<4+2*e;i++)w[i]=variant==0?1:variant==1?1+(i*7+3)%5:(i*7+3)%5;
 Poly predicted;for(auto[mask,c]:copy){I coeff=c;for(int i=0;i<4+2*e;i++)if(!(mask>>i&1))coeff*=w[i];U physical=mask&15;bool valid=true;for(int i=0;i<e;i++){bool a=mask>>(4+i)&1,b=mask>>(4+e+i)&1;if(!a&&!b){valid=false;break;}if(a&&b)physical|=1u<<(4+i);}if(valid)predicted[physical]+=coeff;}clean(predicted);
 Poly direct;for(auto s:feasible){I c=s.k%2?-1:1;for(int a=0;a<4;a++)if((s.a|s.b)>>a&1)c*=w[a];for(int i=0;i<e;i++){if(s.b>>(4+i)&1)c*=w[4+i];if(s.a>>(4+i)&1)c*=w[4+e+i];}direct[((1u<<n)-1)^(s.a|s.b)]+=c;}clean(direct);assert(predicted==direct);identities++;}cases++;}
void choose(int left,int min_type){check();if(!left)return;for(int t=min_type;t<16;t++){ts.push_back(t);choose(left-1,t);ts.pop_back();}}
int main(){for(int a=0;a<256;a++)for(U b=a;b;b=(b-1)&a)subsets[a].push_back(b);for(int n=4;n<=8;n++)enumerate_roles(n,0,0,0);choose(4,0);assert(cases==4845);cout<<"PASS all type multisets through four physical exterior vertices, including isolates\ncases="<<cases<<" weighted_multivariate_identities="<<identities<<" feasible_supports_checked="<<supports_checked<<"\n";}
