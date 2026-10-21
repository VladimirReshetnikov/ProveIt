#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <array>
#include <algorithm>
#include <set>
#include <unordered_set>
using namespace std;
struct A{int w,d,z;};struct Site{string pc,op;int arg;array<int,9> mask;};
int main(int ac,char**av){array<array<A,2>,400>T;set<int>Q;string s;ifstream in(av[1]);while(getline(in,s)){if(s.empty()||s[0]=='#')continue;istringstream ss(s);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};Q.insert(q);}vector<Site>sites;ifstream si(av[2]),mi(av[3]);while(getline(si,s)){Site x;istringstream ss(s);ss>>x.pc>>x.op>>x.arg;for(int &m:x.mask)mi>>m;sites.push_back(x);}array<unordered_set<int>,400>C;int rad=9;long long steps=0,cases=0;int phy[]={6,2,0,4,3,7,8,5,1};
for(int scenario=0;scenario<8;scenario++)for(int i=0;i<(int)sites.size();i++){auto x=sites[i];if(!x.mask[0])continue;for(int positive=0;positive<1+(x.op=="CD");positive++){if(x.op=="CD"&&!(x.mask[x.arg]&(positive?510:1)))continue;int R[9];for(int j=0;j<9;j++){vector<int> vals;for(int v=0;v<8;v++)if(x.mask[j]>>v&1)vals.push_back(v);if(x.mask[j]&256){vals.push_back(8);vals.push_back(9);vals.push_back(20);}if(x.op=="CD"&&j==x.arg)vals.erase(remove_if(vals.begin(),vals.end(),[positive](int v){return (v>0)!=bool(positive);}),vals.end());int k=scenario==0?0:scenario==1?int(vals.size())-1:((i*7+j*3+scenario)%vals.size());R[phy[j]]=vals[k];}int h=2000;vector<unsigned char> tape(10000,0);tape[h-1]=1;for(int j=0;j<(int)x.pc.size();j++)tape[h+j]=(x.pc[j]=='1');int gap=scenario%3;int p=h+64+gap;tape[p++]=1;for(int j=0;j<9;j++){p++;for(int k=0;k<=R[j];k++)tape[p++]=1;}for(int j=0;j<=scenario%5;j++){p++;for(int k=0;k<=1;k++)tape[p++]=1;}int q=84;bool done=false;
for(int n=0;n<100000;n++){int word=0;for(int k=-rad;k<=rad;k++)word|=tape[h+k]<<(k+rad);C[q].insert(word);if(n&&q==254){done=true;break;}
if(n&&q==84&&tape[h-1]){bool clean=true;for(int k=0;k<h-1;k++)if(tape[k]){clean=false;break;}
int hdr=h+52;while(hdr<9980&&!tape[hdr])hdr++;if(hdr<h+64||hdr==9980)clean=false;int last=9980;while(last>hdr&&!tape[last])last--;int p2=hdr+1,vals=0;
while(clean&&p2<last){if(tape[p2]||!tape[p2+1]){clean=false;break;}p2++;while(tape[p2])p2++;vals++;}if(clean&&p2==last+1&&vals>=10){done=true;break;}}
auto a=T[q][tape[h]];tape[h]=a.w;h+=a.d;q=a.z;steps++;if(h<20||h>=9980)break;}
if(!done){cerr<<"FAILED"<<scenario<<" "<<i<<"\n";return 1;}cases++;}}ofstream out(av[4]);for(int q:Q){out<<q;vector<int>w(C[q].begin(),C[q].end());sort(w.begin(),w.end());for(int m:w)out<<" "<<m;out<<"\n";}cerr<<"cases "<<cases<<" steps "<<steps<<" contexts ";long long n=0;for(int q:Q)n+=C[q].size();cerr<<n<<"\n";}
