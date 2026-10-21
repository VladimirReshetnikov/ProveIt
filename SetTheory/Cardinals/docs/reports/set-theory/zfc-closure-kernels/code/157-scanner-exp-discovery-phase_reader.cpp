#include <array>
#include <vector>
#include <set>
#include <fstream>
#include <sstream>
#include <iostream>
using namespace std;struct A{int w,d,z;};array<array<A,2>,500>T;struct C{unsigned long long initial,goal;int q;};vector<C>cases;vector<int>qs;
bool run(C const&c,A first,int patch,A pa,set<int>*vis=nullptr){auto tape=c.initial;int q=41,h=20;for(int k=0;k<120;k++){if(q==c.q&&h>=22&&h<=27&&tape==c.goal)return true;if(q==254||q==50||h<17||h>26)return false;int b=(tape>>h)&1,row=2*q+b;if(vis)vis->insert(row);A a=row==83?first:row==patch?pa:T[q][b];if(!a.d)return false;if(a.w)tape|=1ULL<<h;else tape&=~(1ULL<<h);h+=a.d;q=a.z;}return false;}
int main(int argc,char**argv){ifstream f(argv[1]);string l;set<int>qq;while(getline(f,l)){if(l.empty()||l[0]=='#')continue;int q,b,w,z;char d;istringstream s(l);s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};if(q!=50)qq.insert(q);}qs.assign(qq.begin(),qq.end());T[34][0]={0,-1,75};T[41][0]={1,1,24};T[24][0]={0,1,35};
for(int b=0;b<2;b++)for(int m=0;m<4;m++){unsigned long long input=1ULL<<20;for(int i=22;i<=26;i++)input|=1ULL<<i;if(b)input|=1ULL<<21;if(m&1)input|=1ULL<<17;if(m&2)input|=1ULL<<18;auto goal=input;if(b)goal&=~((1ULL<<20)|(1ULL<<21));else goal|=1ULL<<21;cases.push_back({input,goal,b?0:25});}
long specs=0,localpass=0,hits=0;for(int z:qs)for(int w:{0,1})for(int d:{-1,1}){A first{w,d,z};int fail=-1;set<int>rows;for(int i=0;i<(int)cases.size();i++){set<int>v;if(!run(cases[i],first,-1,{0,0,0},&v)){fail=i;rows=v;break;}}if(fail<0){cerr<<"ONEPASS\n";continue;}for(int row:rows){if(row==83||row==82||row==48||row==68)continue;for(int zz:qs)for(int ww:{0,1})for(int dd:{-1,1}){A pa{ww,dd,zz};specs++;if(!run(cases[fail],first,row,pa))continue;localpass++;bool ok=true;for(int i=0;i<(int)cases.size();i++)if(i!=fail&&!run(cases[i],first,row,pa)){ok=false;break;}if(ok){hits++;cout<<"{\"first\":["<<w<<","<<d<<","<<z<<"],\"patch\":["<<row/2<<","<<row%2<<","<<ww<<","<<dd<<","<<zz<<"]}"<<endl;}}}}cerr<<"specs "<<specs<<" firstpass "<<localpass<<" hits "<<hits<<"\n";}
