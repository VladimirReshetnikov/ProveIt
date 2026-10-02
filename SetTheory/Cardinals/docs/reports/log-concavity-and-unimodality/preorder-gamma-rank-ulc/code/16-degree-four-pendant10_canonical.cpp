// All-population pendant-clone quadratic certificate for every ten-element core.
// Canonicalization refines directed colors, then enumerates within-class permutations.
// Only exact true twins are suppressed. All maximal-element extensions are generated.
// Positive compositions of 10 expand each naturally labeled quotient poset.
#include <bits/stdc++.h>
using namespace std; using ll=long long;
struct Support{unsigned a,b;int k;};
vector<Support> supports; unsigned rows[10];int m;vector<unsigned> qrows;vector<int> blocks;
ll cases=0,degree4=0,bad[3]={},counts[11]={}; ll mins[3]={LLONG_MAX,LLONG_MAX,LLONG_MAX};
ll rn[3]={LLONG_MAX,LLONG_MAX,LLONG_MAX},rd[3]={1,1,1};
bool match(unsigned a,unsigned b){if(!a)return true;unsigned v=rows[__builtin_ctz(a)]&b; a&=a-1; while(v){unsigned x=v&-v;v-=x;if(match(a,b^x))return true;}return false;}
bool perfect(unsigned v){if(!v)return true;int i=__builtin_ctz(v);v&=v-1;for(unsigned c=v;c;c&=c-1){int j=__builtin_ctz(c);if(((rows[i]>>j&1)||(rows[j]>>i&1))&&perfect(v^(1<<j)))return true;}return false;}
void witness(string kind,array<ll,5> g,ll value){cout<<kind<<" value="<<value<<" gamma=";for(ll x:g)cout<<x<<",";cout<<" rows=";for(auto x:rows)cout<<x<<",";cout<<" blocks=";for(auto x:blocks)cout<<x<<",";cout<<endl;}
int mdp[1024];unsigned neighbors[10];
int matchingnum(unsigned mask){if(!mask)return 0;int&out=mdp[mask];if(out>=0)return out;int i=__builtin_ctz(mask);unsigned tail=mask^(1u<<i);out=matchingnum(tail);for(unsigned opts=tail&neighbors[i];opts;opts&=opts-1)out=max(out,1+matchingnum(tail^(opts&-opts)));return out;}
set<array<ll,9>> distinctfamilies;
ll families=0,neglinear=0,quadratic_bad=0; ll minB[3]={LLONG_MAX,LLONG_MAX,LLONG_MAX};
void eval(){int cls[10],p=0;for(int i=0;i<m;i++)for(int j=0;j<blocks[i];j++)cls[p++]=i;fill(rows,rows+10,0);for(int i=0;i<10;i++)for(int j=0;j<10;j++)if(i!=j&&(cls[i]==cls[j]||(qrows[cls[i]]>>cls[j]&1)))rows[i]|=1u<<j;cases++;
 unsigned candidates=0;for(int v=0;v<10;v++){bool incoming=false;for(int i=0;i<10;i++)if(rows[i]>>v&1)incoming=true;if(!incoming||!rows[v])candidates|=1u<<v;}if(!candidates)return;fill(mdp,mdp+1024,-1);for(int i=0;i<10;i++){neighbors[i]=rows[i];for(int j=0;j<10;j++)if(rows[j]>>i&1)neighbors[i]|=1u<<j;}for(int v=0;v<10;v++)if((candidates>>v&1)&&matchingnum(1023^(1u<<v))!=3)candidates^=1u<<v;if(!candidates)return;
 array<ll,5>g={1,0,0,0,0};ll deleted[10][5]={};for(int v=0;v<10;v++)deleted[v][0]=1;
 for(auto s:supports)if(match(s.a,s.b)){g[s.k]++;for(unsigned vv=candidates&~(s.a|s.b);vv;vv&=vv-1)deleted[__builtin_ctz(vv)][s.k]++;}
 for(unsigned vv=candidates;vv;vv&=vv-1){int v=__builtin_ctz(vv);auto b=deleted[v];if(!b[3]||b[4])continue;families++;array<ll,9>record;for(int k=0;k<5;k++)record[k]=g[k];for(int k=0;k<4;k++)record[5+k]=b[k];distinctfamilies.insert(record);
 ll C[]={3*g[1]*g[1]-8*g[2],4*g[2]*g[2]-9*g[1]*g[3],3*g[3]*g[3]-8*g[2]*g[4]};
 ll B[]={6*g[1]-8*b[1],8*g[2]*b[1]-9*(g[1]*b[2]+g[3]),6*g[3]*b[2]-8*(g[2]*b[3]+g[4]*b[1])};
 ll A[]={3,4*b[1]*b[1]-9*b[2],3*b[2]*b[2]-8*b[1]*b[3]};
 for(int j=0;j<3;j++){if(B[j]<minB[j]){minB[j]=B[j];witness("MIN_LINEAR_"+to_string(j+1),g,B[j]);cout<<"deleted_v="<<v<<" gamma_deleted="<<b[0]<<","<<b[1]<<","<<b[2]<<","<<b[3]<<" quadratic="<<C[j]<<","<<B[j]<<","<<A[j]<<endl;}
 if(B[j]<0)neglinear++;
 if(C[j]<0||A[j]<0||(B[j]<0&&(__int128)4*A[j]*C[j]<(__int128)B[j]*B[j])){quadratic_bad++;witness("NEGATIVE_QUADRATIC_"+to_string(j+1),g,B[j]);}
 }
 }
}
void compose(int idx,int left){if(idx==m-1){blocks[idx]=left;eval();return;}for(int x=1;x<=left-(m-idx-1);x++){blocks[idx]=x;compose(idx+1,left-x);}}

using Key=__uint128_t;
Key canonical(vector<unsigned> r){
 int z=r.size();vector<int>color(z,0);int nc=1;
 while(true){vector<vector<int>>sig(z);map<vector<int>,int>ids;for(int i=0;i<z;i++){sig[i].assign(1+2*nc,0);sig[i][0]=color[i];for(int j=0;j<z;j++){if(r[i]>>j&1)sig[i][1+color[j]]++;if(r[j]>>i&1)sig[i][1+nc+color[j]]++;}ids.emplace(sig[i],0);}int cc=0;for(auto&[s,k]:ids)k=cc++;vector<int>newc(z);for(int i=0;i<z;i++)newc[i]=ids[sig[i]];color=newc;if(cc==nc)break;nc=cc;}
 vector<vector<int>>groups(nc);for(int i=0;i<z;i++)groups[color[i]].push_back(i);
 vector<vector<vector<int>>>perms(nc);
 for(int c=0;c<nc;c++){
  map<pair<unsigned,unsigned>,vector<int>>twins;for(int v:groups[c]){unsigned col=0;for(int i=0;i<z;i++)if(r[i]>>v&1)col|=1u<<i;twins[{r[v],col}].push_back(v);}
  vector<vector<int>>classes;vector<int>seq;for(auto&[key,vs]:twins){int id=classes.size();classes.push_back(vs);for(int v:vs)seq.push_back(id);}
  do{vector<int>used(classes.size()),p;for(int id:seq)p.push_back(classes[id][used[id]++]);perms[c].push_back(p);}while(next_permutation(seq.begin(),seq.end()));
 }
 Key best=~Key(0);vector<int>order;
 function<void(int)>rec=[&](int c){if(c<nc){for(auto&p:perms[c]){order.insert(order.end(),p.begin(),p.end());rec(c+1);order.resize(order.size()-p.size());}return;}Key key=0;for(int i=0;i<z;i++)for(int j=0;j<z;j++)if(r[order[i]]>>order[j]&1)key|=Key(1)<<(i*z+j);best=min(best,key);};rec(0);return best;
}
vector<unsigned> decode(Key key,int z){vector<unsigned>r(z);for(int i=0;i<z;i++)for(int j=0;j<z;j++)if(key>>(i*z+j)&1)r[i]|=1u<<j;return r;}
int main(int argc,char**argv){for(unsigned a=1;a<1024;a++){int k=__builtin_popcount(a);if(k>4)continue;unsigned complement=1023^a;for(unsigned b=complement;b;b=(b-1)&complement)if(__builtin_popcount(b)==k)supports.push_back({a,b,k});}cerr<<"supports="<<supports.size()<<endl;vector<vector<unsigned>>last(1);
 for(m=1;m<=10;m++){
  set<Key>keys;for(auto&r:last){int z=r.size();for(unsigned pred=0;pred<(1u<<z);pred++){bool ideal=true;for(int i=0;i<z;i++)if(!(pred>>i&1)&&(r[i]&pred)){ideal=false;break;}if(!ideal)continue;auto nr=r;for(int i=0;i<z;i++)if(pred>>i&1)nr[i]|=1u<<z;nr.push_back(0);keys.insert(canonical(nr));}}
  vector<vector<unsigned>>current;for(Key key:keys){auto r=decode(key,m);current.push_back(r);qrows=r;counts[m]++;blocks.assign(m,0);compose(0,10);}last=move(current);
  cout<<"m="<<m<<" unlabeled_quotients="<<counts[m]<<" cumulative_cases="<<cases<<" degree4="<<degree4<<endl;
 }
 ofstream csv(argc>1?argv[1]:"pendant10_coefficients.csv");csv<<"a0,a1,a2,a3,a4,b0,b1,b2,b3\n";for(auto rec:distinctfamilies){for(int k=0;k<9;k++){if(k)csv<<",";csv<<rec[k];}csv<<"\n";}cout<<"DISTINCT_FAMILIES "<<distinctfamilies.size()<<endl;cout<<"FAMILY_RESULT cases="<<cases<<" families="<<families<<" negative_linear_coefficients="<<neglinear<<" quadratics_negative_on_positive_reals="<<quadratic_bad<<endl;
}
