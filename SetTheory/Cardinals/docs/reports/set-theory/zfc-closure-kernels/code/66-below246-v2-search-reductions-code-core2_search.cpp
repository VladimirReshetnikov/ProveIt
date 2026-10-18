#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
using namespace std;
struct Row{int w,d,t;}; Row T[256][2],U[256][2]; vector<int>states;
struct Test {int q,h,tq,th,origin;vector<int> vals;array<unsigned char,2048> tape;};
vector<Test>tests;
void addtest(vector<int>vs,int r,int mode){
 Test c{};c.q=mode==0?73:95;c.h=500;c.origin=500;c.tq=mode==2?112:48;c.th=mode==1?500:499;c.vals=vector<int>(vs.begin(),vs.begin()+9);
 if(mode==0)c.vals[r]++;
 if(mode==1){c.vals[r]--;c.origin++;}
 int p=500;for(int i=0;i<(int)vs.size();i++){for(int k=1;k<=vs[i]+1;k++)c.tape[p+k]=i==r&&k==1?0:1;p+=vs[i]+2;}
 tests.push_back(c);
}
bool target(array<unsigned char,2048>&a,const Test&c){
 if(c.origin==501&&a[500]!=1)return false;
 for(int i=0;i<500;i++)if(a[i])return false;
 int p=c.origin,n=0;
 while(p<2047){
  if(a[p])return false;
  if(!a[p+1]){
   for(int i=p+1;i<2048;i++)if(a[i])return false;
   return n>=10;
  }
  int k=p+1;while(k<2048&&a[k])k++;
  if(n<9&&c.vals[n]!=k-p-2)return false;
  n++;p=k;
 }
 return false;
}
int Q[18]={73,73,83,83,95,95,109,109,75,75,131,131,112,112,48,48,63,63};
int RID[256][2];
unsigned usedmask=0;
bool run(const Test&c,int fuel){
 auto a=c.tape;int q=c.q,h=c.h;usedmask=0;
 for(int i=0;i<fuel;i++){
  if(RID[q][a[h]]>=0)usedmask|=1u<<RID[q][a[h]];auto row=U[q][a[h]];a[h]=row.w;h+=row.d;q=row.t;
  if(q==254||h<0||h>=2048)return false;
  if(q==c.tq&&h==c.th)return target(a,c);
 }
 return false;
}
int main(int argc,char**argv){
 for(auto &row:RID)fill(row,row+2,-1);for(int z=0;z<18;z++)RID[Q[z]][z%2]=z;
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,t;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&t);T[q][b]={w,d=='R'?1:-1,t};if(b==0&&q!=255)states.push_back(q);}
 vector<int>zero(10,0),pos=zero;pos[0]=1;
 addtest(zero,0,0);addtest(zero,0,2);addtest(pos,0,1);
 for(int r:{0,1,8})for(int mode:{0,1,2}){vector<int>vs={2,0,3,1,1,2,0,4,1,3,0};if(mode==1)vs[r]=2;if(mode==2)vs[r]=0;addtest(vs,r,mode);}
 int fuel=stoi(argv[2]),fold=stoi(argv[3]);long count=0,passes=0,firstcount=0;
 for(int i=0;i<256;i++)for(int j=0;j<2;j++){if(T[i][j].t==255)T[i][j].t=fold;U[i][j]=T[i][j];}
 run(tests[1],fuel);unsigned firstmask=usedmask;
 cerr<<"firstmask "<<firstmask<<endl;
 for(int a=0;a<18;a++)if((firstmask>>a)&1)for(int wa:{0,1})for(int da:{-1,1})for(int ta:states){
  int qa=Q[a],ba=a%2;U[qa][ba]={wa,da,ta};firstcount++;
  unsigned mask=(1u<<18)-1;bool failed=false;
  for(auto&test:tests){if(!run(test,fuel)){mask&=usedmask;failed=true;if(!mask)break;}}
  if(!failed){cerr<<"ONE EDIT SOLUTION"<<endl;}
  mask &= ~(1u<<a);
  for(int b=0;b<18;b++)if((mask>>b)&1)for(int wb:{0,1})for(int db:{-1,1})for(int tb:states){
   int qb=Q[b],bb=b%2;U[qb][bb]={wb,db,tb};count++;bool ok=true;
   for(auto&test:tests)if(!run(test,fuel)){ok=false;break;}
   if(ok){passes++;cout<<"PASS fold255="<<fold<<" edits "<<qa<<" "<<ba<<" "<<wa<<" "<<(da==1?'R':'L')<<" "<<ta<<" ; "<<qb<<" "<<bb<<" "<<wb<<" "<<(db==1?'R':'L')<<" "<<tb<<endl;}
   U[qb][bb]=T[qb][bb];
  }
  U[qa][ba]=T[qa][ba];
 }
 cerr<<"first "<<firstcount<<" total "<<count<<" passes "<<passes<<endl;
}
