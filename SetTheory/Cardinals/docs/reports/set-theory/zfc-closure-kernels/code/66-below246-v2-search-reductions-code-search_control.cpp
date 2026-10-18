#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <cstring>
using namespace std;
struct Row{int w,d,t;}; Row T[256][2],U[256][2];vector<int>states;
struct Case{int q,h,qt,ht;array<unsigned char,4096>one{},ot{};};vector<Case>cases;
int run(const Case&c,int fuel){auto tape=c.one;int q=c.q,h=c.h,wrong=0;
 for(int n=0;n<fuel;n++){if(h<0||h>=4096)return 2;auto r=U[q][tape[h]];tape[h]=r.w;h+=r.d;q=r.t;
 if(q==254)return c.qt==254?0:3;
 if(q==c.qt){if(h==c.ht&&tape==c.ot)return 0;if(++wrong>15)return 4;}}
 return 1;}
int check(int fuel){for(int i=0;i<(int)cases.size();i++)if(run(cases[i],fuel))return i;return -1;}
int main(int argc,char**argv){ifstream tf(argv[1]);string line;
 while(getline(tf,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,t;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&t);T[q][b]={w,d=='R'?1:-1,t};if(b==0)states.push_back(q);}
 std::memcpy(U,T,sizeof(T));ifstream cf(argv[2]);int count;cf>>count;
 while(count--){Case c;int k,p;cf>>c.q>>c.h>>k;c.h+=1024;while(k--){cf>>p;c.one[p+1024]=1;}cf>>c.qt>>c.ht>>k;c.ht+=1024;while(k--){cf>>p;c.ot[p+1024]=1;}cases.push_back(c);}
 int fuel=stoi(argv[3]),q=stoi(argv[4]),b=stoi(argv[5]),q2=argc>6?stoi(argv[6]):-1,b2=argc>7?stoi(argv[7]):-1;
 long tried=0,passed=0;int maxcase=-1;
 auto test=[&](int w,int d,int t,int w2,int d2,int t2){tried++;int fail=check(fuel);maxcase=max(maxcase,fail);if(fail<0){passed++;cout<<"PASS "<<q<<" "<<b<<" "<<w<<" "<<(d==1?'R':'L')<<" "<<t;if(q2>=0)cout<<" ; "<<q2<<" "<<b2<<" "<<w2<<" "<<(d2==1?'R':'L')<<" "<<t2;cout<<endl;}};
 for(int w:{0,1})for(int d:{-1,1})for(int t:states){U[q][b]={w,d,t};if(q2<0)test(w,d,t,0,0,0);else for(int w2:{0,1})for(int d2:{-1,1})for(int t2:states){U[q2][b2]={w2,d2,t2};test(w,d,t,w2,d2,t2);}}
 cerr<<"tried "<<tried<<" passed "<<passed<<" latest_failed_fixture "<<maxcase<<endl;
}
