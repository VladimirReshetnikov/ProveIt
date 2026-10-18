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
bool run(const Test&c,int fuel){
 auto a=c.tape;int q=c.q,h=c.h;
 for(int i=0;i<fuel;i++){
  auto row=U[q][a[h]];a[h]=row.w;h+=row.d;q=row.t;
  if(q==254||h<0||h>=2048)return false;
  if(q==c.tq&&h==c.th&&target(a,c))return true;
 }
 return false;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,t;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&t);T[q][b]={w,d=='R'?1:-1,t};if(b==0&&q!=255)states.push_back(q);}
 vector<int>zero(10,0),pos=zero;pos[0]=1;
 addtest(zero,0,0);addtest(zero,0,2);addtest(pos,0,1);
 for(int r:{0,1,8})for(int mode:{0,1,2}){vector<int>vs={2,0,3,1,1,2,0,4,1,3,0};if(mode==1)vs[r]=2;if(mode==2)vs[r]=0;addtest(vs,r,mode);}
 int fuel=stoi(argv[2]),count=0,passes=0;
for(int fold:states){int lastpass=passes;
 for(int q:{73,83,95,109,75,131,112,48,63})for(int b:{0,1})for(int w:{0,1})for(int d:{-1,1})for(int t:states){
  for(int i=0;i<256;i++)for(int j=0;j<2;j++){U[i][j]=T[i][j];if(U[i][j].t==255)U[i][j].t=fold;}
  U[q][b]={w,d,t};count++;bool ok=true;for(auto&c:tests)if(!run(c,fuel)){ok=false;break;}
  if(ok){passes++;cout<<"PASS fold255="<<fold<<" edit "<<q<<" "<<b<<" "<<w<<" "<<(d==1?'R':'L')<<" "<<t<<endl;}
 }
 if(passes!=lastpass)cerr<<"fold "<<fold<<" passes "<<passes-lastpass<<endl;}
cerr<<"total "<<count<<" passes "<<passes<<endl;
}
