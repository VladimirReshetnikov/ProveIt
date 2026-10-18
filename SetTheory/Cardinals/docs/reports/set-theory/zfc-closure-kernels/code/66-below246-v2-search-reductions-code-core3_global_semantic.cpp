#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <stdexcept>
using namespace std;
struct Row{int w,d,t;};Row T[256][2],U[256][2];vector<int>states;
struct Case{int q,h,qt,ht,origin;array<unsigned char,4096>one{},ot{};array<int,9>vals;};vector<Case>cases;
bool check(const array<unsigned char,4096>&one,const Case&c,int head){
 if(head<1||head+40>=4096||!one[head-1])return false;
 for(int p=0;p<head-1;p++)if(one[p])return false;
 for(int p=0;p<40;p++)if(one[head+p]!=c.ot[c.ht+p])return false;
 int p=head+40;while(p<4096&&!one[p])p++;if(p>=4096)return false;p++;
 int n=0;
 while(p<4095){
  if(one[p])return false;
  if(!one[p+1]){for(int j=p+1;j<4096;j++)if(one[j])return false;return n>=10;}
  int k=p+1;while(k<4096&&one[k])k++;
  if(n<9&&c.vals[n]!=k-p-2)return false;
  n++;p=k;
 }
 return false;
}
bool run(const Case&c,int fuel){auto tape=c.one;int q=c.q,h=c.h;
 for(int n=0;n<fuel;n++){if(h<0||h>=4096)return false;auto r=U[q][tape[h]];tape[h]=r.w;h+=r.d;q=r.t;if(q==254)return c.qt==254;if(q==c.qt&&check(tape,c,h))return true;}
 return false;
}
int main(int argc,char**argv){ifstream tf(argv[1]);string line;
 while(getline(tf,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,t;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&t);T[q][b]={w,d=='R'?1:-1,t};if(b==0&&q!=255)states.push_back(q);}
 T[75][0]={0,1,63};T[48][0]={1,-1,131};for(int q:states)for(int b:{0,1})U[q][b]=T[q][b];
 ifstream cf(argv[2]);int count;cf>>count;
 while(count--){Case c;int k,p;cf>>c.q>>c.h>>k;c.h+=1024;while(k--){cf>>p;c.one[p+1024]=1;}cf>>c.qt>>c.ht>>k;c.ht+=1024;while(k--){cf>>p;c.ot[p+1024]=1;}cf>>k;while(k--)cf>>p;
 if(c.qt!=254){p=1064;while(!c.ot[p])p++;c.origin=++p;for(int j=0;j<9;j++){if(c.ot[p])return 4;k=p+1;while(c.ot[k])k++;c.vals[j]=k-p-2;p=k;}}
 cases.push_back(c);}
 int fuel=stoi(argv[3]),tries=0,passes=0;
 for(int q:{48,63,112,131})for(int b:{0,1})for(int w:{0,1})for(int d:{-1,1})for(int t:states){U[q][b]={w,d,t};tries++;bool good=true;for(auto&c:cases)if(!run(c,fuel)){good=false;break;}if(good){passes++;cout<<"PASS extra "<<q<<" "<<b<<" "<<w<<" "<<(d==1?'R':'L')<<" "<<t<<endl;}U[q][b]=T[q][b];}
 cerr<<"trials "<<tries<<" passes "<<passes<<endl;
}
