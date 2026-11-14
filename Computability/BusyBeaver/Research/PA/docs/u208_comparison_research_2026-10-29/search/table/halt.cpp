#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <chrono>
using namespace std;
struct Act{int w,d,r;};
struct Case{array<int,41> a;};
Act t[400][2];vector<Case> cs[400];vector<int> states;
int q,r;Act e[2];long long nodes=0;
bool dfs(int s,int h,array<int,41> tape,array<int,41> origin,int n,int w,int d,int z,bool partial,bool &used,int &budget){
 if(--budget<0)return false;
 if(n && s==254 && z==254)return true;
 if(n && s==z && h==d){bool same=true;for(int i=0;i<41;i++)if(tape[i]!=(i==20?w:origin[i])){same=false;break;}if(same)return true;}
 if(n>=40 || s==254 || abs(h)>8)return false;
 int b=tape[h+20];
 if(b<0){for(int bit=0;bit<2;bit++){auto a=tape, o=origin;a[h+20]=bit;o[h+20]=bit;if(!dfs(s,h,a,o,n,w,d,z,partial,used,budget))return false;}return true;}
 if(s==r && b==1 && partial){used=true;return true;}
 Act a=s==r?e[b]:t[s][b];if(a.r==q)a.r=r;tape[h+20]=a.w;
 return dfs(a.r,h+a.d,tape,origin,n+1,w,d,z,partial,used,budget);
}
bool check(int old,int b,bool partial,bool &used){
 Act a=t[old][b];if(a.r==q)a.r=r;
 for(auto c:cs[old]){if(c.a[20]>=0&&c.a[20]!=b)continue;c.a[20]=b;int budget=1000;if(!dfs(r,0,c.a,c.a,0,a.w,a.d,a.r,partial,used,budget))return false;}
 return true;
}
int main(int argc,char**argv){ifstream in(argv[1]);int n;in>>n;for(int i=0;i<n;i++){int s,k;in>>s;states.push_back(s);in>>t[s][0].w>>t[s][0].d>>t[s][0].r>>t[s][1].w>>t[s][1].d>>t[s][1].r>>k;while(k--){Case c;c.a.fill(-1);int m;in>>m;while(m--){int p,b;in>>p>>b;if(abs(p)<=20)c.a[p+20]=b;}cs[s].push_back(c);}}
 vector<int> actions=states;actions.push_back(254);
 long long trials=0,partialgood=0,second=0,hits=0;auto start=chrono::steady_clock::now();
 for(int qq:states){if(qq==0)continue;q=qq;
 for(int rr:states){if(rr==0||rr==q)continue;r=rr;if(q!=68 && r!=68)continue;
 // Common incompatible preceding markers are not required; branching can distinguish conditional contexts.
 for(int z:actions){if(z==q)continue;for(int d:{-1,1})for(int w:{0,1}){e[0]={w,d,z};bool used=false;trials++;
 if(!check(q,0,true,used)||!check(r,0,true,used))continue;partialgood++;
 for(int z1:actions){if(z1==q)continue;for(int d1:{-1,1})for(int w1:{0,1}){second++;e[1]={w1,d1,z1};bool u=false;
 if(check(q,1,false,u)&&check(r,1,false,u)&&check(q,0,false,u)&&check(r,0,false,u)){hits++;cout<<"HIT "<<q<<" "<<r<<" "<<w<<" "<<d<<" "<<z<<" / "<<w1<<" "<<d1<<" "<<z1<<endl;}
 }}
 }}
 }
 if(q%10==0)cerr<<"progress "<<q<<" trials "<<trials<<" partial "<<partialgood<<" second "<<second<<" hits "<<hits<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cout<<"DONE trials "<<trials<<" partial "<<partialgood<<" second "<<second<<" hits "<<hits<<endl;
}
