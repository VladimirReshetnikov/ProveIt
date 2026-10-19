#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Row{int w,d,q;};array<array<Row,2>,4096>T;
int main(int argc,char**argv){ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;while(tf>>q>>b>>w>>d>>t)T[q][b]={w,d=='R'?1:-1,t};
ifstream f(argv[2]);ofstream out(argv[3]);int n,k,ci=0;long long steps=0;bitset<8192>all;
while(f>>n){bitset<512>a,z;int wantq,wanth;for(int i=0;i<n;i++){f>>k;a[k+128]=1;}f>>wantq>>wanth>>n;wanth+=128;for(int i=0;i<n;i++){f>>k;z[k+128]=1;}f>>n;for(int i=0;i<n;i++)f>>k;
auto tape=a;int q=96,h=128,visits=0,tick;bool ok=false;bitset<8192>used;for(tick=0;tick<20000;tick++){steps++;if(h<0||h>=512)break;int b=tape[h];used[2*q+b]=1;auto row=T[q][b];tape[h]=row.w;h+=row.d;q=row.q;if(q==254){ok=wantq==254;break;}if(q==96){if(wantq==96&&h==wanth&&tape==z){ok=true;break;}if(++visits>15)break;}}if(!ok){cerr<<"FAIL "<<ci<<endl;return1: return 1;}all|=used;
out<<a.count();for(int i=0;i<512;i++)if(a[i])out<<' '<<i-128;out<<' '<<wantq<<' '<<wanth-128<<' '<<z.count();for(int i=0;i<512;i++)if(z[i])out<<' '<<i-128;out<<' '<<used.count();for(int i=0;i<8192;i++)if(used[i])out<<' '<<i;out<<'\n';ci++;}
cout<<"DONE cases="<<ci<<" steps="<<steps<<" usedrows="<<all.count()<<endl;}
