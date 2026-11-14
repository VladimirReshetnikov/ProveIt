#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <algorithm>
using namespace std;struct Act{int w,d,r;};struct Case{array<int,41>a;};Act t[400][2],startaction,helperaction;vector<int>states;vector<Case>cs[400];int helper,bit;
bool dfs(int s,int h,array<int,41>tape,array<int,41>origin,int n,int z,int dh,int targetwrite,bool partial,int&budget){
 if(--budget<0)return false;
 if(n&&s==z&&h==dh){bool same=true;for(int i=0;i<41;i++)if(tape[i]!=(i==20&&targetwrite>=0?targetwrite:origin[i])){same=false;break;}if(same)return true;}
 if(n>=60||s==254||abs(h)>8)return false;
 int b=tape[h+20];if(b<0){for(int x:{0,1}){auto a=tape,o=origin;a[h+20]=x;o[h+20]=x;if(!dfs(s,h,a,o,n,z,dh,targetwrite,partial,budget))return false;}return true;}
 if(partial&&s==helper&&b==bit)return true;
 Act a=(s==118&&b==0)?startaction:((s==helper&&b==bit)?helperaction:t[s][b]);tape[h+20]=a.w;
 return dfs(a.r,h+a.d,tape,origin,n+1,z,dh,targetwrite,partial,budget);
}
bool macro(bool partial){for(int b:{0,1}){Case c;c.a.fill(-1);c.a[19]=1;c.a[20]=0;c.a[21]=0;c.a[22]=b;int budget=2000;if(!dfs(118,0,c.a,c.a,0,b?12:98,3,-1,partial,budget))return false;}return true;}
bool ordinary(){Act a=t[helper][bit];for(auto c:cs[helper]){if(c.a[20]>=0&&c.a[20]!=bit)continue;c.a[20]=bit;int budget=2000;if(!dfs(helper,0,c.a,c.a,0,a.r,a.d,a.w,false,budget))return false;}return true;}
int main(int argc,char**argv){ifstream in(argv[1]);int n;in>>n;for(int i=0;i<n;i++){int s,k;in>>s;states.push_back(s);in>>t[s][0].w>>t[s][0].d>>t[s][0].r>>t[s][1].w>>t[s][1].d>>t[s][1].r>>k;while(k--){Case c;c.a.fill(-1);int m;in>>m;while(m--){int p,b;in>>p>>b;if(abs(p)<=20)c.a[p+20]=b;}cs[s].push_back(c);}}
 long long first=0,second=0,hits=0;for(int hh:states){helper=hh;for(int bb:{0,1}){bit=bb;if(helper==118&&bit==0)continue;
 for(int z:states)for(int d:{-1,1})for(int w:{0,1}){startaction={w,d,z};first++;if(!macro(true))continue;
 for(int z1:states)for(int d1:{-1,1})for(int w1:{0,1}){helperaction={w1,d1,z1};second++;if(!ordinary())continue;if(macro(false)){hits++;cout<<"HIT first "<<w<<" "<<d<<" "<<z<<" helper "<<helper<<" "<<bit<<" action "<<w1<<" "<<d1<<" "<<z1<<endl;}}
 }}if(helper%20==0)cerr<<"progress "<<helper<<" first "<<first<<" second "<<second<<" hits "<<hits<<endl;}
cout<<"DONE first "<<first<<" second "<<second<<" hits "<<hits<<endl;
}
