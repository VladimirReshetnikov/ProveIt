// Exhaustive marked preorder certificate. All arithmetic exact signed 64-bit.
#include <bits/stdc++.h>
using namespace std; using ll=long long;
struct Pair{unsigned a,b;int k;};
vector<Pair> pairs[8]; unsigned rows[7], unions_[128];int n,m;vector<unsigned> qr;vector<int> blocks;
using Key=array<ll,5>; // p1,p2,p3,q1,q2
struct Rec{ll count=0;int n,v;vector<unsigned> rows;};map<Key,Rec> cert;
ll qcounts[8]={}, expansions[8]={}, marks[8]={},valid[8]={}, matchchecks=0;
bool match(unsigned a,unsigned b){if(!a)return true;int i=__builtin_ctz(a);a&=a-1;unsigned t=rows[i]&b;while(t){unsigned u=t&-t;t-=u;if(match(a,b^u))return true;}return false;}
bool hall(unsigned a,unsigned b){for(unsigned s=a;s;s=(s-1)&a)if(__builtin_popcount(unions_[s]&b)<__builtin_popcount(s))return false;return true;}
void evaluate(){int cls[7],pos=0;for(int i=0;i<m;i++)for(int j=0;j<blocks[i];j++)cls[pos++]=i;
 fill(rows,rows+7,0);for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(i!=j&&(cls[i]==cls[j]||(qr[cls[i]]>>cls[j]&1)))rows[i]|=1u<<j;
 expansions[n]++;vector<int> minimal;for(int i=0;i<n;i++){bool yes=blocks[cls[i]]==1;for(int j=0;j<n;j++)if(rows[j]>>i&1)yes=false;if(yes)minimal.push_back(i);}marks[n]+=minimal.size();if(minimal.empty())return;
 unions_[0]=0;for(unsigned s=1;s<(1u<<n);s++){unsigned b=s&-s;unions_[s]=unions_[s^b]|rows[__builtin_ctz(b)];}
 ll p[4]={1,0,0,0},deleted[7][4]={};for(int v:minimal)deleted[v][0]=1;
 for(auto t:pairs[n]){bool h=hall(t.a,t.b);assert(h==match(t.a,t.b));matchchecks++;if(h){p[t.k]++;for(int v:minimal)if(!((t.a|t.b)>>v&1))deleted[v][t.k]++;}}
 for(int v:minimal){if(deleted[v][3])continue;valid[n]++;Key k={p[1],p[2],p[3],deleted[v][1],deleted[v][2]};auto &r=cert[k];if(!r.count || n<r.n){r.n=n;r.v=v;r.rows=vector<unsigned>(rows,rows+n);}r.count++;}}
void compose(int i,int left){if(i==m-1){blocks[i]=left;evaluate();return;}for(int s=1;s<=left-(m-i-1);s++){blocks[i]=s;compose(i+1,left-s);}}
int main(){for(int N=1;N<=7;N++)for(unsigned a=1;a<(1u<<N);a++){int k=__builtin_popcount(a);if(k>3)continue;for(unsigned b=1;b<(1u<<N);b++)if(!(a&b)&&__builtin_popcount(b)==k)pairs[N].push_back({a,b,k});}
 for(m=1;m<=7;m++){vector<pair<int,int>> es;for(int i=0;i<m;i++)for(int j=i+1;j<m;j++)es.push_back({i,j});qr.resize(m);for(unsigned mask=0;mask<(1u<<es.size());mask++){fill(qr.begin(),qr.end(),0);for(int e=0;e<(int)es.size();e++)if(mask>>e&1)qr[es[e].first]|=1u<<es[e].second;
 bool trans=true;for(int i=0;i<m;i++)for(int j=i+1;j<m;j++)if((qr[i]>>j&1)&&(qr[j]&~qr[i]))trans=false;if(!trans)continue;qcounts[m]++;for(n=m;n<=7;n++){blocks.assign(m,0);compose(0,n);}}cerr<<"quotient "<<m<<" count "<<qcounts[m]<<"\n";}
 cout<<"p1,p2,p3,q1,q2,count,n,v,rowmasks\n";for(auto &[k,r]:cert){for(auto x:k)cout<<x<<",";cout<<r.count<<","<<r.n<<","<<r.v<<",";for(int i=0;i<r.n;i++)cout<<(i?" ":"")<<r.rows[i];cout<<"\n";}
 cerr<<"support_Hall_matching_crosschecks "<<matchchecks<<" unique_pairs "<<cert.size()<<"\n";for(n=1;n<=7;n++)cerr<<"n "<<n<<" expansions "<<expansions[n]<<" singleton_minimal_marks "<<marks[n]<<" valid_marks "<<valid[n]<<"\n";
}
