#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#include <cstdint>
using namespace std;
struct Row{int w=0,d=0,z=-1;};struct Conf{int q,h;uint64_t x;};array<array<Row,2>,1600>T,M;array<vector<uint64_t>,1600>I;vector<int>S;int R,N,os=16,ns=64;
bool eq(Conf c,Conf v,int K,int D,int off){if(v.q==D){v.q=K;v.h+=off;}return c.q==v.q&&c.h==v.h&&c.x==v.x;}
vector<Conf>goals(int q,uint64_t x){int h=R;vector<Conf>g;for(int k=0;k<os;++k){auto r=T[q][(x>>h)&1];if(r.z<0)break;x=(x&~(1ULL<<h))|(uint64_t(r.w)<<h);h+=r.d;q=r.z;g.push_back({q,h,x});if(h<0||h>=N||q==254)break;}return g;}
bool check(uint64_t x,int K,int D,int off){auto g=goals(D,x);int q=K,h=R+off;for(int k=0;k<ns;++k){auto r=M[q][(x>>h)&1];if(r.z<0)return false;x=(x&~(1ULL<<h))|(uint64_t(r.w)<<h);h+=r.d;q=r.z;for(auto v:g)if(eq({q,h,x},v,K,D,off))return true;if(h<0||h>=N||q==254)return false;}return false;}
int main(int argc,char**argv){R=argc>3?stoi(argv[3]):20;N=2*R+1;ifstream in(argv[1]);string ln;set<int>ss;while(getline(in,ln)){if(ln.empty()||ln[0]=='#')continue;istringstream s(ln);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;T[q][b]={w,d=='L'?-1:1,z};ss.insert(q);}S.assign(ss.begin(),ss.end());ifstream samples(argv[4]);int q;uint64_t x;long long patterns=0;while(samples>>q>>x){I[q].push_back(x);++patterns;}cerr<<"samples "<<patterns<<" R"<<R<<endl;int hits=0,trials=0;auto st=chrono::steady_clock::now();for(int D:S)if(D!=0)for(int off:{-2,2}){bool allow=true;for(int q:S)if(q!=D)for(int b=0;b<2;++b)if(T[q][b].z==D&&abs(T[q][b].d+off)!=1)allow=false;if(!allow)continue;for(int K:S)if(K!=D){++trials;M=T;for(int q:S)if(q!=D)for(int b=0;b<2;++b)if(M[q][b].z==D){M[q][b].z=K;M[q][b].d+=off;}M[D][0].z=M[D][1].z=-1;bool ok=true;for(auto x:I[D])if(!check(x,K,D,off)){ok=false;break;}if(ok){string name=string(argv[2])+".hit"+to_string(hits++)+".tm";ofstream out(name);out<<"#! start 0\n";for(int q:S)if(q!=D)for(int b=0;b<2;++b){auto r=M[q][b];out<<q<<" "<<b<<" "<<r.w<<" "<<(r.d==1?'R':'L')<<" "<<r.z<<"\n";}cout<<"HIT K"<<K<<" D"<<D<<" off"<<off<<endl;}}}cout<<"DONE trials "<<trials<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-st).count()<<endl;}
