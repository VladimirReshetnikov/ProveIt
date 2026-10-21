#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <array>
#include <algorithm>
#include <set>
#include <chrono>
using namespace std;
struct A{int w,d,z;};
int main(int ac,char**av){array<array<A,2>,400>T;set<int>Q;string s;ifstream in(av[1]);while(getline(in,s)){if(s.empty()||s[0]=='#')continue;istringstream ss(s);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};Q.insert(q);}const int N=600000;int phy[]={6,2,0,4,3,7,8,5,1};long long attempts=0,frames=0,rays=0,limits=0,halted=0;
vector<array<int,5>> edits;ifstream es(av[2]);int x0,x1,x2,x3,x4;while(es>>x0>>x1>>x2>>x3>>x4)edits.push_back({x0,x1,x2,x3,x4});int allstarts=ac>3?stoi(av[3]):0;
for(auto e:edits){pair<int,int>key={e[0],e[1]};auto orig=T[key.first][key.second];int w=e[2],d=e[3],z=e[4];T[key.first][key.second]={w,d,z};vector<int> starts=allstarts?vector<int>(Q.begin(),Q.end()):vector<int>{0};for(int start:starts){attempts++;vector<unsigned char>t(2*N+1,0);int q=start,h=N,lo=N,hi=N,ones=0;int maxsteps=1500000;for(int step=0;step<maxsteps;step++){if(q==254){halted++;break;}if(q==84&&ones&&t[h-1]&&lo==h-1){bool pc=false;for(int i=h;i<h+64;i++)pc|=t[i];int header=h+64;while(header<=hi&&!t[header])header++;if(!pc&&header<=hi){vector<int> vals;int p=header+1;bool ok=true;while(p<hi){if(t[p]||!t[p+1]){ok=false;break;}int a=++p;while(t[p])p++;vals.push_back(p-a-1);}if(ok&&vals.size()>=10&&p==hi+1){frames++;cout<<key.first<<" "<<key.second<<" -> "<<w<<" "<<d<<" "<<z<<" START "<<start<<" FRAME "<<step<<" h "<<h-N<<" gap "<<header-h-64<<" logical";for(int j=0;j<9;j++)cout<<" "<<vals[phy[j]];cout<<" spares "<<vals.size()-9<<"\n";cout.flush();break;}}}int b=t[h];auto a=T[q][b];if(!b&&a.z==q&&(!ones||(a.d==1&&h>hi)||(a.d==-1&&h<lo))){rays++;break;}if(a.w&&!b){t[h]=1;if(!ones){lo=h;hi=h;}else{lo=min(lo,h);hi=max(hi,h);}ones++;}else if(!a.w&&b){t[h]=0;ones--;if(ones){if(h==lo)while(!t[lo])lo++;if(h==hi)while(!t[hi])hi--;}}h+=a.d;q=a.z;if(h<100||h>2*N-100){limits++;break;}if(step==maxsteps-1){limits++;}} }T[key.first][key.second]=orig;if(attempts%(allstarts?2170:50)==0)cerr<<"PROGRESS "<<key.first<<" count "<<attempts<<" frames "<<frames<<" rays "<<rays<<" limits "<<limits<<" halted "<<halted<<"\n";}
}
