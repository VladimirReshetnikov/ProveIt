#include <bits/stdc++.h>
using namespace std;
// Discovery only: sampled interpreter frames are not an inductive invariant.
struct Act{int w,d,z;};
Act tab[256][2];
constexpr int ORIGIN=1024,SIZE=16384;
int R=5,W,MASK;vector<vector<bool>> domains;
vector<int> PHY={6,2,0,4,3,7,8,5,1};
long long totalsteps=0,totalcases=0;
void collect(vector<unsigned char>&t,int q,int h,int &mask){
  domains[q][mask]=1;
  Act a=tab[q][t[h+ORIGIN]];
  t[h+ORIGIN]=a.w;
  mask=(mask&~(1<<R))|(a.w<<R);
  if(a.d==1)mask=(mask>>1)|(int(t[h+ORIGIN+R+1])<<(W-1));
  else mask=((mask<<1)&MASK)|int(t[h+ORIGIN-R-1]);
  totalsteps++;
}
int window(vector<unsigned char>const&t,int h){int x=0;for(int i=-R;i<=R;i++)x|=int(t[h+ORIGIN+i])<<(R+i);return x;}
pair<string,int> inc(string p){for(int i=int(p.size())-1;i>=0;i--){if(p[i]=='0'){p[i]='1';return{p,0};}p[i]='0';}return{p,1};}
string strip(string p,char b,int n){for(int i=int(p.size())-1;i>=0;i--)if(p[i]==b&&--n==0)return p.substr(0,i);return "";}
vector<unsigned char> frame(string pc,vector<int>regs,vector<int>spares,int gap,int shift=0){
 vector<unsigned char> t(SIZE);auto one=[&](int p){t[p+shift+ORIGIN]=1;};
 one(-1);one(64+gap);for(int i=0;i<int(pc.size());i++)if(pc[i]=='1')one(i);
 vector<int> vals(9);for(int i=0;i<9;i++)vals[PHY[i]]=regs[i];vals.insert(vals.end(),spares.begin(),spares.end());
 int p=65+gap;for(int v:vals){p++;for(int j=0;j<=v;j++)one(p+j);p+=v+1;}return t;
}
void run_case(string pc,string op,int arg,int scenario,bool positive,vector<pair<int,int>> const& bounds={}){
 vector<int> regs(9);for(int i=0;i<9;i++){
   switch(scenario%8){case 0:regs[i]=0;break;case 1:regs[i]=1;break;case 2:regs[i]=i%3;break;case 3:regs[i]=(2*i+3)%5;break;case 4:regs[i]=R+1;break;case 5:regs[i]=i%2?2*R:0;break;case 6:regs[i]=i==arg?0:3;break;default:regs[i]=(i+scenario)%4;}
 }
 if(!bounds.empty())for(int i=0;i<9;i++){
  regs[i]=max(regs[i],bounds[i].first);
  if(bounds[i].second>=0)regs[i]=min(regs[i],bounds[i].second);
 }
 if(op=="CD")regs[arg]=positive?max(1,regs[arg]):0;
 if(!bounds.empty())for(int i=0;i<9;i++)if(regs[i]<bounds[i].first||(bounds[i].second>=0&&regs[i]>bounds[i].second)){cerr<<"invalid guard input\n";exit(2);}
 vector<int> spares;switch(scenario%4){case 0:spares={1};break;case 1:spares={0};break;case 2:spares={1,0,2};break;default:spares={4,3,0,1,5};}
 int gap=(scenario%3)*5;
 auto tape=frame(pc,regs,spares,gap);auto rr=regs;auto ss=spares;string next;int overflow=0,delta=0;
 if(op=="CI"){rr[arg]++;ss.push_back(1);tie(next,overflow)=inc(pc);}
 else if(op=="CD"&&positive){rr[arg]--;delta=1;tie(next,overflow)=inc(pc);}
 else if(op=="CD"||op=="CB")tie(next,overflow)=inc(strip(pc,'0',op=="CB"?arg:1));
 else if(op=="CC")next=strip(pc,'1',arg);
 auto target=frame(next,rr,ss,gap+delta+overflow,-overflow);
 int q=96,h=0,mask=window(tape,h);bool done=false;
 for(int k=0;k<500000;k++){
  if(k&&((op=="CH"&&q==254)||(op!="CH"&&q==96&&h==-overflow&&tape==target))){done=true;break;}
  if(q==254){cerr<<"unexpected halt\n";exit(2);}
  Act a=tab[q][tape[h+ORIGIN]];collect(tape,q,h,mask);q=a.z;h+=a.d;
  if(h<=-ORIGIN+R+1||h>=SIZE-ORIGIN-R-1){cerr<<"tape bounds\n";exit(2);}
 }
 if(!done){cerr<<"failed "<<pc<<" "<<op<<" "<<arg<<" scenario="<<scenario<<" pos="<<positive<<"\n";exit(2);}totalcases++;
}
int main(int argc,char**argv){
 if(argc<4){cerr<<"TABLE SITES OUTPUT [RADIUS] [SCENARIOS]\n";return 2;}
 if(argc>4)R=stoi(argv[4]);W=2*R+1;MASK=(1<<W)-1;domains.assign(256,vector<bool>(1<<W));
 ifstream f(argv[1]);string line;while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};}
 vector<unsigned char> boot(SIZE);int q=95,h=0,mask=window(boot,h);
 for(int k=0;k<409835;k++){Act a=tab[q][boot[h+ORIGIN]];collect(boot,q,h,mask);q=a.z;h+=a.d;}
 if(q!=96||h!=-5){cerr<<"boot mismatch\n";return 2;}
 ifstream g(argv[2]);string pc,op;int arg,scenarios=argc>5?stoi(argv[5]):8;
 bool guarded=argc>6&&string(argv[6])=="--guarded";
 while(g>>pc>>op>>arg){
  vector<pair<int,int>> bounds;int positive=0;
  if(guarded){g>>positive;for(int i=0;i<9;i++){int lo,hi;g>>lo>>hi;bounds.push_back({lo,hi});}}
  for(int s=0;s<scenarios;s++){
   run_case(pc,op,arg,s,positive,bounds);
   if(!guarded&&op=="CD")run_case(pc,op,arg,s,true);
  }
 }
 if(!g.eof()){cerr<<"Malformed source-site input\n";return 2;}
 ofstream out(argv[3]);long long patterns=0;for(int s=0;s<256;s++)for(int x=0;x<=MASK;x++)if(domains[s][x]){out<<s<<" "<<x<<"\n";patterns++;}
 cerr<<"cases="<<totalcases<<" steps="<<totalsteps<<" patterns="<<patterns<<" radius="<<R<<"\n";
}
