// Concrete discovery filter, never an unbounded correctness certificate.
// Checks all source leaves with small primary values and one spare block.
#include <array>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>
#include <tuple>
using namespace std;
struct Row {int w=-1,d=0,q=-1;};
using Tape=array<unsigned char,16384>;
constexpr int OFF=4096;
array<int,9> PHY={6,2,0,4,3,7,8,5,1};
pair<string,int> inc(string p) {
 for(int i=(int)p.size()-1;i>=0;--i) {if(p[i]=='0'){p[i]='1';return {p,0};}p[i]='0';}
 return {p,1};
}
string strip(string p,char b,int n) {
 if(n==0)return p;
 for(int i=(int)p.size()-1;i>=0;--i)if(p[i]==b&&--n==0)return p.substr(0,i);
 return "";
}
Tape frame(string pc,array<int,9> logical,vector<int> spares,int gap,int shift=0) {
 Tape a{};int origin=OFF-shift;a[origin-1]=a[origin+64+gap]=1;
 for(int i=0;i<(int)pc.size();++i)a[origin+i]=(pc[i]=='1');
 array<int,9> physical{};for(int i=0;i<9;++i)physical[PHY[i]]=logical[i];
 vector<int> values(physical.begin(),physical.end());values.insert(values.end(),spares.begin(),spares.end());
 int pos=origin+65+gap;
 for(int v:values){++pos;for(int k=0;k<=v;++k)a[pos++]=1;}
 return a;
}
bool clean(int q,int h,const Tape&a) {
 if(q!=96||h<1||h+52>=(int)a.size()||!a[h-1])return false;
 for(int i=0;i<h-1;++i)if(a[i])return false;
 int p=h+52;while(p<(int)a.size()&&!a[p])++p;
 if(p==(int)a.size()||p<h+64)return false;
 int last=(int)a.size()-1;while(last>=0&&!a[last])--last;
 ++p;int count=0;
 while(p<last){if(a[p]||!a[p+1])return false;++p;while(p<(int)a.size()&&a[p])++p;++count;}
 return p==last+1&&count>=10;
}
int main(int argc,char**argv){
 if(argc<3){cerr<<"table.tm sites.txt [primary-profile] [gap]\n";return 2;}
 array<array<Row,2>,1024> table;string line;ifstream ft(argv[1]);
 if(!ft){cerr<<"Cannot read table\n";return 2;}
 while(getline(ft,line)){
  if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,z;char d;
  if(!(s>>q>>b>>w>>d>>z)||q<0||q>=1024||b<0||b>1||w<0||w>1||z<0||z>=1024||(d!='L'&&d!='R')||table[q][b].w>=0){cerr<<"Malformed table\n";return 2;}
  table[q][b]={w,d=='R'?1:-1,z};
 }
 for(int q=0;q<1024;++q)if((table[q][0].w<0)!=(table[q][1].w<0)){cerr<<"Incomplete state\n";return 2;}
 if(table[96][0].w<0||table[254][0].w>=0){cerr<<"Wrong runtime entry or halt convention\n";return 2;}
 ifstream fs(argv[2]);string pc,op;int arg,index=0,checked=0;int profile=argc>3?stoi(argv[3]):0;int gap=argc>4?stoi(argv[4]):0;
 if(!fs||profile<0||profile>1||gap<0||gap>4096){cerr<<"Missing source or invalid profile/gap\n";return 2;}
 while(fs>>pc>>op>>arg){
  if(pc.empty()||pc.size()>64||pc.find_first_not_of("01")!=string::npos||
    ((op=="CI"||op=="CD")&&(arg<0||arg>=9))||
    ((op=="CB"||op=="CC")&&arg<1)){cerr<<"Malformed source record\n";return 2;}
  for(int positive=0;positive<(op=="CD"?2:1);++positive){
   array<int,9> values{};for(int i=0;i<9;++i)values[i]=profile?((i*3+1)%4):0;
   if(op=="CD")values[arg]=positive?(profile?3:1):0;
   Tape tape=frame(pc,values,{profile?2:0},gap),want;int overflow=0,delta=0;string nxt;vector<int>spares={profile?2:0};
   if(op=="CI"){++values[arg];spares.push_back(1);tie(nxt,overflow)=inc(pc);}
   else if(op=="CD"&&positive){--values[arg];delta=1;tie(nxt,overflow)=inc(pc);}
   else if(op=="CD"||op=="CB")tie(nxt,overflow)=inc(strip(pc,'0',op=="CB"?arg:1));
   else if(op=="CC")nxt=strip(pc,'1',arg);
   else if(op!="CH"){cerr<<"unknown operation";return 2;}
   if(op!="CH")want=frame(nxt,values,spares,gap+delta+overflow,overflow);
   int q=96,h=OFF,tick=0;bool ok=false;
   for(;tick<=20000;++tick){
    if(tick&&((op=="CH"&&q==254)||(op!="CH"&&q==96&&h==OFF-overflow&&tape==want))){ok=true;break;}
    if(tick&&clean(q,h,tape))break;
    if(tick==20000||h<0||h>=(int)tape.size()||q<0||q>=1024||table[q][tape[h]].w<0)break;
    Row r=table[q][tape[h]];tape[h]=r.w;h+=r.d;q=r.q;
   }
   if(!ok){cout<<"{\"status\":\"FINITE_FAILURE\",\"index\":"<<index<<",\"positive\":"<<positive<<",\"cases\":"<<checked<<",\"ticks\":"<<tick<<",\"state\":"<<q<<",\"head\":"<<h-OFF<<",\"pc\":\""<<pc<<"\",\"op\":\""<<op<<"\",\"arg\":"<<arg<<"}\n";return 1;}
   ++checked;
  }
  ++index;
 }
 if(index!=6455||checked!=8386){cerr<<"Incomplete source census\n";return 2;}
 cout<<"{\"status\":\"FINITE_PROFILE_PASS\",\"cases\":"<<checked<<",\"profile\":"<<profile<<",\"gap\":"<<gap<<"}\n";
}
