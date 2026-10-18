#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <algorithm>
#include <chrono>
using namespace std;
struct A{int w,d,t;}; using T=array<array<A,2>,256>;
struct Case{array<unsigned char,1024> input{},expected{};int start,end,head,extent;bool inc;vector<int> values;int reg;};
Case makecase(vector<int>v,int r,int op){Case c{};c.values=v;c.reg=r;c.inc=op==1;c.start=c.inc?73:95;c.end=op==2?48:op==1?48:112;c.head=op==2?0:-1;int p=100;for(int i=0;i<(int)v.size();i++){for(int k=0;k<=v[i];k++)c.input[p+k+1]=1;if(i==r)c.input[p+1]=0;p+=v[i]+2;}c.extent=p;auto w=v;if(op==1)w[r]++;if(op==2)w[r]--;p=100+(op==2);if(op==2)c.expected[100]=1;for(int x:w){for(int k=0;k<=x;k++)c.expected[p+k+1]=1;p+=x+2;}return c;}
bool test(T&tab,const Case&c,int fuel=3000){auto a=c.input;int q=c.start,h=100;for(int i=0;i<fuel;i++){if(i&&h==100+c.head&&q==c.end){if(!c.inc)return a==c.expected;int p=100;vector<int>v;while(p<1000){if(a[p]||!a[p+1])break;p++;int start=p;while(p<1000&&a[p])p++;v.push_back(p-start-1);}for(int j=p;j<1024;j++)if(a[j])return false;auto want=c.values;want[c.reg]++;return v.size()>want.size()&&equal(want.begin(),want.end(),v.begin());}if(h<100||h>980||q==254||q==255)return false;A z=tab[q][a[h]];a[h]=z.w;h+=z.d;q=z.t;}return false;}
int main(int argc,char**argv){
 if(argc<4){cerr<<"usage: search_pair table secondstate secondbit\n";return 2;}
 int q2=stoi(argv[2]),b2=stoi(argv[3]);T tab{};vector<int>states;ifstream in(argv[1]);string line;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,t;char d;s>>q>>b>>w>>d>>t;tab[q][b]={w,d=='R'?1:-1,t};if(!b&&q!=255)states.push_back(q);}
 vector<A>actions;for(int w:{0,1})for(int d:{-1,1})for(int t:states)actions.push_back({w,d,t});
 vector<Case>cases;cases.push_back(makecase(vector<int>(10,0),0,0));cases.push_back(makecase(vector<int>(10,0),0,1));
 for(int r:{0,1,4,8})for(int z:{0,1,3})for(int op:{0,1,2}){vector<int>v(12);for(int i=0;i<12;i++)v[i]=(i+z)%4;v[r]=op==0?0:op==2?z+1:z;cases.push_back(makecase(v,r,op));}
 long long tried=0,zero=0,inc=0,survive=0;auto began=chrono::steady_clock::now();
 for(A a:actions){tab[75][0]=a;for(A b:actions){tab[q2][b2]=b;tried++;if(!test(tab,cases[0]))continue;zero++;if(!test(tab,cases[1]))continue;inc++;bool ok=true;for(size_t i=2;i<cases.size();i++)if(!test(tab,cases[i])){ok=false;break;}if(ok){survive++;cout<<"PASS 75/0="<<a.w<<","<<a.d<<","<<a.t<<" "<<q2<<"/"<<b2<<"="<<b.w<<","<<b.d<<","<<b.t<<endl;}}}
 cout<<"DONE tried="<<tried<<" zero="<<zero<<" inc="<<inc<<" survivors="<<survive<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;
}
