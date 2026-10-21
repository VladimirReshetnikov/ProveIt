#include <algorithm>
#include <array>
#include <chrono>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Row { int w=0,d=0,z=-1; };
struct Conf { int q,h,x; };
array<array<Row,2>,1600> T,M;
vector<int> states;array<vector<int>,1600> I;
int R=7,N,words,mask,oldsteps=8,newsteps=24;
int red(int q,int K,int D) {return q==D?K:q;}
bool match(const Conf&c,const vector<Conf>&g,int K,int D){for(auto v:g)if(c.q==red(v.q,K,D)&&c.h==v.h&&c.x==v.x)return true;return false;}
vector<Conf> old_goals(int q,int x){vector<Conf> g;int h=R;for(int k=0;k<oldsteps;++k){Row r=T[q][(x>>h)&1];if(r.z<0)break;x=(x&~(1<<h))|(r.w<<h);h+=r.d;q=r.z;g.push_back({q,h,x});if(h<0||h>=N||q==254)break;}return g;}
bool check_case(int q,int x,int K,int D){auto g=old_goals(q,x);int h=R;q=red(q,K,D);for(int k=0;k<newsteps;++k){Row r=M[q][(x>>h)&1];if(r.z<0)return false;x=(x&~(1<<h))|(r.w<<h);h+=r.d;q=r.z;if(match({q,h,x},g,K,D))return true;if(h<0||h>=N||q==254)return false;}return false;}
bool check_row(int K,int D,int b){for(int q:{K,D})for(int x:I[q])if(((x>>R)&1)==b&&!check_case(q,x,K,D))return false;return true;}
bool same(Row a,Row b,int K,int D){return a.w==b.w&&a.d==b.d&&red(a.z,K,D)==red(b.z,K,D);}
int main(int argc,char**argv){ifstream in(argv[1]);string ln;if(argc>3)R=stoi(argv[3]);N=2*R+1;words=1<<N;mask=words-1;set<int> ss;while(getline(in,ln)){if(ln.empty()||ln[0]=='#')continue;istringstream s(ln);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;T[q][b]={w,d=='L'?-1:1,z};ss.insert(q);}states.assign(ss.begin(),ss.end());
array<vector<unsigned char>,1600> seen;for(int q:states)seen[q].resize(words);deque<pair<int,int>>todo;seen[0][0]=1;todo.push_back({0,0});long long pops=0;while(!todo.empty()){auto[q,x]=todo.front();todo.pop_front();I[q].push_back(x);++pops;auto r=T[q][(x>>R)&1];if(r.z==254)continue;int y=(x&~(1<<R))|(r.w<<R);array<int,2>ys=r.d==1?array<int,2>{y>>1,(y>>1)|(1<<(N-1))}:array<int,2>{(y<<1)&mask,((y<<1)&mask)|1};for(int z:ys)if(!seen[r.z][z]){seen[r.z][z]=1;todo.push_back({r.z,z});}}
for(int q:states)sort(I[q].begin(),I[q].end());cerr<<"invariant "<<pops<<" configurations radius "<<R<<endl;ofstream inv(string(argv[2])+".invariant.json");inv<<"{";bool comma=false;for(int q:states){if(comma)inv<<",";comma=true;inv<<"\""<<q<<"\":[";for(int j=0;j<(int)I[q].size();++j){if(j)inv<<",";inv<<I[q][j];}inv<<"]";}inv<<"}\n";inv.close();
long long tested=0;int hits=0,pairs=0;auto started=chrono::steady_clock::now();
// Prioritize altered K219 engine states, then the rest.
vector<int> ks=states;stable_sort(ks.begin(),ks.end(),[](int a,int b){set<int> p={302,301,40,4,113,198,103,108,87,88};return p.count(a)>p.count(b);});
for(int K:ks)for(int D:states){if(D==K||D==0)continue;bool s0=same(T[K][0],T[D][0],K,D),s1=same(T[K][1],T[D][1],K,D);if(!s0&&!s1){bool overlap=false;for(int x:I[K])if(seen[D][x]){overlap=true;break;}if(overlap)continue;}++pairs;M=T;for(int q:states)for(int b=0;b<2;++b)M[q][b].z=red(M[q][b].z,K,D);M[D][0].z=M[D][1].z=-1;bool ok=true;
for(int b=0;b<2;++b){if(b?s1:s0)continue;bool found=false;for(int w:{b,1-b}){for(int d:{-1,1}){for(int z:states){if(z==D)continue;M[K][b]={w,d,z};++tested;if(check_row(K,D,b)){found=true;break;}}if(found)break;}if(found)break;}if(!found){ok=false;break;}}
if(ok){for(int b=0;b<2;++b)if(!check_row(K,D,b))ok=false;}
if(ok){string name=string(argv[2])+".hit"+to_string(hits++)+".tm";ofstream out(name);out<<"#! start 0\n";for(int q:states)if(q!=D)for(int b=0;b<2;++b){auto r=M[q][b];out<<q<<" "<<b<<" "<<r.w<<" "<<(r.d==1?'R':'L')<<" "<<r.z<<"\n";}cout<<"HIT K"<<K<<" D"<<D<<" rows "<<M[K][0].w<<","<<M[K][0].d<<","<<M[K][0].z<<" ; "<<M[K][1].w<<","<<M[K][1].d<<","<<M[K][1].z<<endl;}
if(pairs%1000==0)cerr<<"pairs "<<pairs<<" tests "<<tested<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}cout<<"DONE pairs "<<pairs<<" tests "<<tested<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
}
