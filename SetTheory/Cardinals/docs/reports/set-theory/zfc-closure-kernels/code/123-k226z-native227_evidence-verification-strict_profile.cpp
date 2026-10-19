// Finite regression and discovery profiles. Whole tapes and head offsets are
// checked, but only symbolic_runtime supplies universal runtime proofs.
#include <bits/stdc++.h>
using namespace std;
struct Act{int w,d,q;};Act tab[256][2];
using Tape=array<unsigned char,4096>;
Tape tape,boot_goal;bitset<2048> dom[256];
const int center=1024;long long steps_=0,cases_=0;
int sample(int h){int x=0;for(int k=-5;k<=5;k++)x|=int(tape[h+k])<<(k+5);return x;}
bool clean(int q,int h){
 if(q!=96||!tape[h-1])return false;
 for(int k=0;k<h-1;k++)if(tape[k])return false;
 int p=h+52;while(p<int(tape.size())&&!tape[p])p++;
 return p>=h+64&&p<int(tape.size());
}
pair<int,int> run(int q,int h,int bound,bool boot){
 for(int tick=0;tick<=bound;tick++){
  if(h<5||h>=int(tape.size())-5)throw runtime_error("footprint");
  if((tick&&(boot?(q==96&&h==center-5&&tape==boot_goal):clean(q,h)))||q==254){cases_++;return {q,h};}
  if(tick==bound)throw runtime_error("fuel");
  dom[q][sample(h)]=true;Act a=tab[q][int(tape[h])];
  tape[h]=a.w;h+=a.d;q=a.q;steps_++;
 }
 abort();
}
Tape frame(string pc,array<int,9> const& logical,vector<int> const& spare,int gap,int shift=0){
 Tape out{};const int phy[]={6,2,0,4,3,7,8,5,1};array<int,9> values;
 for(int r=0;r<9;r++)values[phy[r]]=logical[r];
 int c=center+shift;
 out[c-1]=1;
 for(int k=0;k<int(pc.size());k++)out[c+k]=pc[k]=='1';
 out[c+64+gap]=1;int h=c+65+gap;
 vector<int> all(values.begin(),values.end());all.insert(all.end(),spare.begin(),spare.end());
 for(int v:all){h++;for(int k=0;k<=v;k++)out[h++]=1;}
 return out;
}
pair<string,int> inc(string pc){
 for(int i=int(pc.size())-1;i>=0;i--)if(pc[i]=='0'){pc[i]='1';return {pc,0};}else pc[i]='0';
 return {pc,1};
}
string strip(string pc,char bit,int count){
 if(!count)return pc;
 for(int i=int(pc.size())-1;i>=0;i--)if(pc[i]==bit&&!--count)return pc.substr(0,i);
 return "";
}
int main(int argc,char**argv){
 if(argc!=5){cerr<<"TABLE SITES PROFILE BOOT_SUPPORT\n";return 2;}
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream in(line);int q,b,w,r;char d;in>>q>>b>>w>>d>>r;tab[q][b]={w,d=='R'?1:-1,r};}
 try{
  Tape want{};ifstream boot(argv[4]);int pos;while(boot>>pos)want[center+pos]=1;
  boot_goal=want;
  auto [bq,bh]=run(95,center,1000000,true);
  if(bq!=96||bh!=center-5||tape!=want){cerr<<"BOOT_FAIL "<<bq<<" "<<bh-center<<"\n";return 1;}
  ifstream g(argv[2]);string pc,op;int arg,index=0;
  while(g>>pc){
   if(!(g>>op>>arg))throw runtime_error("malformed or truncated source site");
   for(int seed=0;seed<4;seed++)for(int positive=0;positive<(op=="CD"?2:1);positive++){
    int gap=seed==3?7:0;array<int,9> regs{};
    for(int r=0;r<9;r++)regs[r]=seed==0?0:seed==1?2:seed==2?(r*3+index)%9:11;
    if(op=="CD")regs[arg]=positive?seed+1:0;
    vector<int> spare;
    if(seed==0)spare={0};if(seed==1)spare={0,1};if(seed==2)spare={3,0,8};if(seed==3)spare={11,11};
    tape=frame(pc,regs,spare,gap);
    auto [aq,ah]=run(96,center,1000000,false);
    if(op=="CH"){if(aq!=254){cerr<<"HALT_FAIL "<<index<<"\n";return 1;}continue;}
    string nxt;int shift=0,delta=0;
    if(op=="CI"){regs[arg]++;spare.push_back(1);tie(nxt,shift)=inc(pc);}
    else if(op=="CD"&&positive){regs[arg]--;delta=1;tie(nxt,shift)=inc(pc);}
    else if(op=="CD"||op=="CB")tie(nxt,shift)=inc(strip(pc,'0',op=="CB"?arg:1));
    else if(op=="CC")nxt=strip(pc,'1',arg);
    else throw runtime_error("opcode");
    want=frame(nxt,regs,spare,gap+delta+shift,-shift);
    if(aq!=96||ah!=center-shift||tape!=want){
      cerr<<"RUNTIME_FAIL site "<<index<<" seed "<<seed<<" positive "<<positive<<" q "<<aq<<" h "<<ah-center<<" want_h "<<-shift<<" path "<<pc<<" op "<<op<<" arg "<<arg<<" diffs";
      for(int i=0;i<int(tape.size());i++)if(tape[i]!=want[i])cerr<<" "<<i-center<<":"<<int(tape[i])<<"/"<<int(want[i]);cerr<<"\n";return 1;
    }
   }
   index++;
  }
  if(!g.eof()||index==0)throw runtime_error("source site input failure");
  ofstream out(argv[3]);int count=0;
  for(int q=0;q<256;q++)for(int x=0;x<2048;x++)if(dom[q][x]){out<<q<<" "<<x<<"\n";count++;}
  cerr<<"STRICT_FINITE_PASS instructions "<<index<<" cases_including_boot "<<cases_<<" steps "<<steps_<<" profile_pairs "<<count<<"\n";
 }catch(exception const&e){cerr<<"ERROR "<<e.what()<<" cases "<<cases_<<"\n";return 1;}
}
