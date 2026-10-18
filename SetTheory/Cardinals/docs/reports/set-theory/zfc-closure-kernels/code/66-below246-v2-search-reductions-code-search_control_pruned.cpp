#include <array>
#include <bitset>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <cstring>
using namespace std;
struct Row{int w,d,t;};Row T[256][2],U[256][2];vector<int>states;
struct Case{int q,h,qt,ht;array<unsigned char,4096>one{},ot{};};vector<Case>cases;
bitset<512>used;
int run(const Case&c,int fuel){auto tape=c.one;int q=c.q,h=c.h,wrong=0;used.reset();
 for(int n=0;n<fuel;n++){if(h<0||h>=4096)return 2;used.set(2*q+tape[h]);auto r=U[q][tape[h]];tape[h]=r.w;h+=r.d;q=r.t;
 if(q==254)return c.qt==254?0:3;
 if(q==c.qt){if(h==c.ht&&tape==c.ot)return 0;if(++wrong>15)return 4;}}
 return 1;}
int check(int fuel,int limit=-1){if(limit<0)limit=cases.size();for(int i=0;i<limit;i++)if(run(cases[i],fuel))return i;return -1;}
int main(int argc,char**argv){ifstream tf(argv[1]);string line;
 while(getline(tf,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,t;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&t);T[q][b]={w,d=='R'?1:-1,t};if(b==0)states.push_back(q);}
 std::memcpy(U,T,sizeof(T));ifstream cf(argv[2]);int count;cf>>count;
 while(count--){Case c;int k,p;cf>>c.q>>c.h>>k;c.h+=1024;while(k--){cf>>p;c.one[p+1024]=1;}cf>>c.qt>>c.ht>>k;c.ht+=1024;while(k--){cf>>p;c.ot[p+1024]=1;}cases.push_back(c);}
 int fuel=stoi(argv[3]),samples=stoi(argv[4]),q=218,b=0;long first=0,second=0,passed=0,micro=0;int furthest=0;
 bitset<512>real;for(int s:states)for(int r:{0,1})real.set(2*s+r);int ordinal=0;
 for(int w:{0,1})for(int d:{-1,1})for(int t:states){
  ordinal++;
  if(argc>5&&stoi(argv[5])>=0&&(t!=stoi(argv[5])||w!=stoi(argv[6])||d!=stoi(argv[7])))continue;
  if(argc>8&&(ordinal<stoi(argv[8])||ordinal>stoi(argv[9])))continue;
  U[q][b]={w,d,t};first++;bitset<512>mask=real;bool failed=false;
  for(int i=0;i<samples;i++)if(run(cases[i],fuel)){mask&=used;failed=true;if(mask.none())break;}
  if(!failed){cerr<<"ONE ROW MICRO "<<w<<" "<<d<<" "<<t<<endl;}
  mask.reset(2*q+b);
  for(int rb=0;rb<512;rb++)if(mask[rb]){int q2=rb/2,b2=rb%2;
   for(int w2:{0,1})for(int d2:{-1,1})for(int t2:states){U[q2][b2]={w2,d2,t2};second++;int fail=check(fuel,samples);
    if(fail<0){micro++;fail=check(10000);if(fail<0){passed++;cout<<"PASS "<<q<<" "<<b<<" "<<w<<" "<<(d==1?'R':'L')<<" "<<t<<" ; "<<q2<<" "<<b2<<" "<<w2<<" "<<(d2==1?'R':'L')<<" "<<t2<<endl;}else if(fail>furthest){furthest=fail;cerr<<"NEAR fixture "<<fail<<" edits "<<q<<" "<<b<<" "<<w<<" "<<(d==1?'R':'L')<<" "<<t<<" ; "<<q2<<" "<<b2<<" "<<w2<<" "<<(d2==1?'R':'L')<<" "<<t2<<endl;}}
   }U[q2][b2]=T[q2][b2];
  }
  U[q][b]=T[q][b];
  if(first%100==0)cerr<<"progress first "<<first<<" second "<<second<<" micro "<<micro<<" passes "<<passed<<" furthest "<<furthest<<endl;
 }
 cerr<<"first "<<first<<" second "<<second<<" micro "<<micro<<" passes "<<passed<<" furthest "<<furthest<<endl;
}
