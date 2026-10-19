// Finite discovery profile, explicitly not a universal invariant.
// Every instruction is run from several valid concrete register frames.
#include <array>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>
#include <cmath>
using namespace std;
struct Act {int w,d,q;};Act tm[256][2];
vector<bool> tape(16384);set<int> dom[256];
const int center=4096;int radius_;long long steps_=0,cases_=0;
int sample(int h){int x=0;for(int k=-radius_;k<=radius_;k++)x|=int(tape[h+k])<<(k+radius_);return x;}
bool clean(int q,int h){
 if(q!=96||!tape[h-1])return false;
 for(int k=0;k<h-1;k++)if(tape[k])return false;
 int p=h+52;while(p<int(tape.size())&&!tape[p])p++;
 return p>=h+64&&p<int(tape.size());
}
void run(int q,int h,int bound,bool boot) {
 for(int tick=0;tick<=bound;tick++) {
  if(h<radius_||h>=int(tape.size())-radius_)throw runtime_error("footprint");
  if((tick&&clean(q,h))||q==254){cases_++;return;}
  if(tick==bound)throw runtime_error("fuel");
  dom[q].insert(sample(h));Act a=tm[q][int(tape[h])];
  tape[h]=a.w;h+=a.d;q=a.q;steps_++;
 }
}
bool allowed(unsigned mask,int value){int cls=value<16?value:16+value%2;return mask&(1u<<cls);}
int choose(unsigned mask,int want,int minimum=0){
 int best=-1,score=1000000;
 for(int value=minimum;value<130;value++)if(allowed(mask,value)&&abs(value-want)<score){best=value;score=abs(value-want);}
 if(best<0)throw runtime_error("empty source abstract domain");return best;
}
int main(int argc,char**argv) {
 if(argc<6)return 2;radius_=stoi(argv[3]);
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream in(line);int q,b,w,r;char d;in>>q>>b>>w>>d>>r;tm[q][b]={w,d=='R'?1:-1,r};}
 run(95,center,1000000,true);
 ifstream g(argv[2]),fg(argv[5]);string pc,op;int arg,index=0;int phy[]={6,2,0,4,3,7,8,5,1};
 long long guards_=0,unreachable_=0;
 while(g>>pc>>op>>arg) {
  array<unsigned,9> abstract{};for(auto &v:abstract)if(!(fg>>v))throw runtime_error("facts length");
  if(!abstract[0]){index++;unreachable_++;continue;}
  for(int seed=0;seed<6;seed++)for(int pos=0;pos<(op=="CD"?2:1);pos++) {
   if(op=="CD"&&((pos==0&&!(abstract[arg]&1))||(pos==1&&!(abstract[arg]&~1u))))continue;
   guards_++;
   fill(tape.begin(),tape.end(),false);
   int gap=seed==3?7:seed==5?13:0;array<int,9> values{};
   for(int r=0;r<9;r++){int requested=seed==0?0:seed==1?2:seed==2?(r*3+index)%9:seed==3?11:seed==4?32:63;values[phy[r]]=choose(abstract[r],requested);}
   if(op=="CD")values[phy[arg]]=pos?choose(abstract[arg],seed==5?63:seed+1,1):0;
   tape[center-1]=true;
   for(int k=0;k<int(pc.size());k++)tape[center+k]=pc[k]=='1';
   tape[center+64+gap]=true;int h=center+65+gap;
   vector<int> all(values.begin(),values.end());
   if(seed==0)all.push_back(0);
   if(seed==1){all.push_back(0);all.push_back(1);}
   if(seed==2){all.push_back(3);all.push_back(0);all.push_back(8);}
   if(seed>=3){all.push_back(seed==3?11:seed*9);all.push_back(seed==3?11:0);all.push_back(seed+1);}
   for(int v:all){h++;for(int k=0;k<=v;k++)tape[h++]=true;}
   run(96,center,1000000,false);
  }
  index++;
 }
 ofstream out(argv[4]);int count=0;
 for(int q=0;q<256;q++)for(int x:dom[q]){out<<q<<" "<<x<<"\n";count++;}
 cerr<<"FINITE_SOURCE_CONSTRAINED_PROFILE unreachable "<<unreachable_<<" valid_fixtures "<<guards_<<" radius "<<radius_<<" instructions "<<index<<" cases_including_boot "<<cases_<<" steps "<<steps_<<" pairs "<<count<<"\n";
}
