// Complete a=2 rank-four template polynomial enumeration on eight-element cores.
// Smaller cores embed by adding isolated elements. Loops are omitted throughout.
#include<bits/stdc++.h>
using namespace std;using ll=long long;
#include "canonical.inc"
struct Supp{unsigned a,b;int k;};vector<Supp> balanced,imbalanced;unsigned rows[8];int m;vector<unsigned>qrows;vector<int>blocks;
int feasible[256][256];
bool match(unsigned a,unsigned b){if(!a)return 1;unsigned opts=rows[__builtin_ctz(a)]&b;a&=a-1;while(opts){unsigned x=opts&-opts;opts-=x;if(match(a,b^x))return 1;}return 0;}
bool perfect(unsigned v){if(!v)return true;int i=__builtin_ctz(v);v&=v-1;for(unsigned c=v;c;c&=c-1){int j=__builtin_ctz(c);if(((rows[i]>>j&1)||(rows[j]>>i&1))&&perfect(v^(1u<<j)))return true;}return false;}
bool transitive(vector<unsigned> r){int n=r.size();for(int i=0;i<n;i++)r[i]|=1u<<i;for(int i=0;i<n;i++)for(int j=0;j<n;j++)if((r[i]>>j&1)&&(r[j]&~r[i]))return false;return true;}
vector<unsigned> expand(int a,int b,int s,vector<int> types){vector<unsigned>r(rows,rows+8);r.resize(8+types.size());for(int i=0;i<(int)types.size();i++)for(int t=0;t<2;t++)if(types[i]>>t&1){int v=t?b:a;if(s>>t&1)r[v]|=1u<<(8+i);else r[8+i]|=1u<<v;}return r;}
struct Spec{int a,b,s,legal;};
using Poly=array<int,50>;struct Record{array<unsigned,8> rows;Spec spec;};map<Poly,Record>polys;
ll cores=0,eligible=0,specs=0,degree4=0;int g[5],deleted[8][5],twodeleted[8][8][5],overlap[2][5][8][8];
// q columns: 0, e1,e2,e3, 2e1,2e2,2e3, e1+e2,e1+e3,e2+e3.
int paircol(int t,int u){if(t==u)return 3+t;if(t==1&&u==2)return 7;if(t==1&&u==3)return 8;return 9;}
int pairweight(int t,int u,int s){set<int>rolepatterns;for(int sw=0;sw<2;sw++){int a=sw,b=1-sw;if((t>>a&1)&&(u>>b&1)){int pattern=((s>>a&1)?1:0)|((s>>b&1)?2:0);rolepatterns.insert(pattern);}}return rolepatterns.size();}
Poly swapped(Poly p){int perm[]={0,2,1,3,5,4,6,7,9,8};Poly q;for(int k=0;k<5;k++)for(int i=0;i<10;i++)q[10*k+i]=p[10*k+perm[i]];return q;}
void eval(){cores++;int cls[8],pos=0;for(int i=0;i<m;i++)for(int j=0;j<blocks[i];j++)cls[pos++]=i;fill(rows,rows+8,0);for(int i=0;i<8;i++)for(int j=0;j<8;j++)if(i!=j&&(cls[i]==cls[j]||(qrows[cls[i]]>>cls[j]&1)))rows[i]|=1u<<j;
 vector<Spec>ss;for(int a=0;a<8;a++)for(int b=a+1;b<8;b++){if(perfect(255^(1u<<a)^(1u<<b)))continue;for(int s=0;s<4;s++){int legal=0;vector<int>types;for(int t=1;t<=3;t++)if(transitive(expand(a,b,s,{t,t}))){legal|=1<<t;types.push_back(t);}if(!legal)continue;if(!transitive(expand(a,b,s,types)))throw runtime_error("incompatible maximal types");ss.push_back({a,b,s,legal});}}
 if(ss.empty())return;eligible++;memset(g,0,sizeof g);memset(deleted,0,sizeof deleted);memset(twodeleted,0,sizeof twodeleted);memset(overlap,0,sizeof overlap);memset(feasible,0,sizeof feasible);
 for(auto p:balanced){bool good=match(p.a,p.b);feasible[p.a][p.b]=good;if(!good)continue;g[p.k]++;unsigned absent=255&~(p.a|p.b);for(unsigned aa=absent;aa;aa&=aa-1){int a=__builtin_ctz(aa);deleted[a][p.k]++;for(unsigned bb=absent&~((1u<<(a+1))-1);bb;bb&=bb-1){int b=__builtin_ctz(bb);twodeleted[a][b][p.k]++;}}}
 // For a leaf with two same-oriented possible partners, subtract supports admitting both.
 for(auto p:imbalanced)for(int dir=0;dir<2;dir++){unsigned good=0;for(unsigned vs=p.a;vs;vs&=vs-1){unsigned bit=vs&-vs;if(dir?feasible[p.b][p.a^bit]:feasible[p.a^bit][p.b])good|=bit;}for(unsigned aa=good;aa;aa&=aa-1){int a=__builtin_ctz(aa);for(unsigned bb=good&~((1u<<(a+1))-1);bb;bb&=bb-1){int b=__builtin_ctz(bb);overlap[dir][p.k][a][b]++;}}}
 for(auto spec:ss){specs++;int a=spec.a,b=spec.b,s=spec.s,L=spec.legal;Poly p={};for(int k=0;k<5;k++)p[10*k]=g[k];for(int t=1;t<=3;t++)if(L>>t&1)for(int k=1;k<=4;k++){int value=0;if(t&1)value+=deleted[a][k-1];if(t&2)value+=deleted[b][k-1];if(t==3&&((s&1)==((s>>1)&1)))value-=overlap[(s&1)?0:1][k][a][b];p[10*k+t]=value;}
 for(int t=1;t<=3;t++)if(L>>t&1)for(int u=t;u<=3;u++)if(L>>u&1){int w=pairweight(t,u,s);for(int k=2;k<=4;k++)p[10*k+paircol(t,u)]=w*twodeleted[a][b][k-2];}
 bool deg4=false;for(int j=0;j<10;j++)if(p[40+j])deg4=true;if(!deg4)continue;degree4++;
 // Keep literal type ordering in the representative; variable-swapped keys only deduplicate.
 Poly key=min(p,swapped(p));if(!polys.count(key)){Record r;copy(rows,rows+8,r.rows.begin());r.spec=spec;polys.emplace(key,r);}
 }
}
void compose(int idx,int left){if(idx==m-1){blocks[idx]=left;eval();return;}for(int x=1;x<=left-(m-idx-1);x++){blocks[idx]=x;compose(idx+1,left-x);}}
int main(int argc,char**argv){string out=argc>1?argv[1]:"a2_polynomials.jsonl";
 for(unsigned a=0;a<256;a++)for(unsigned b=0;b<256;b++)if(!(a&b)){int ka=__builtin_popcount(a),kb=__builtin_popcount(b);if(ka==kb&&ka<=4)balanced.push_back({a,b,ka});if(ka==kb+1&&ka<=4)imbalanced.push_back({a,b,ka});}
 vector<vector<unsigned>>last(1);for(m=1;m<=8;m++){set<Key>keys;for(auto&r:last){int z=r.size();for(unsigned pred=0;pred<(1u<<z);pred++){bool ideal=true;for(int i=0;i<z;i++)if(!(pred>>i&1)&&(r[i]&pred)){ideal=false;break;}if(!ideal)continue;auto nr=r;for(int i=0;i<z;i++)if(pred>>i&1)nr[i]|=1u<<z;nr.push_back(0);keys.insert(canonical(nr));}}vector<vector<unsigned>>current;for(auto key:keys){auto r=decode(key,m);current.push_back(r);qrows=r;blocks.assign(m,0);compose(0,8);}last=move(current);cout<<"m="<<m<<" cores="<<cores<<" eligible_cores="<<eligible<<" specifications="<<specs<<" degree4_specs="<<degree4<<" unique_polynomials="<<polys.size()<<endl;}
 ofstream f(out);ll id=0;for(auto&[p,r]:polys){f<<"{\"id\":"<<id++<<",\"core_rows\":[";for(int i=0;i<8;i++){if(i)f<<",";f<<r.rows[i];}f<<"],\"attachments\":["<<r.spec.a<<","<<r.spec.b<<"],\"orientation_mask\":"<<r.spec.s<<",\"legal_types\":"<<r.spec.legal<<",\"gamma\":[";for(int k=0;k<5;k++){if(k)f<<",";f<<"[";for(int j=0;j<10;j++){if(j)f<<",";f<<p[10*k+j];}f<<"]";}f<<"]}\n";}cout<<"COMPLETE unique_polynomials="<<polys.size()<<endl;
}
