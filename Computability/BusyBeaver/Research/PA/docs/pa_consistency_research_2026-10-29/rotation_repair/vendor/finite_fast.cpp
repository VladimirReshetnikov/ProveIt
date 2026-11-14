#include <string>
#include <vector>
#include <array>
#include <cstring>
#include <sstream>
using namespace std;
struct Site{string p,op;int a;};
constexpr int W=4096,OFF=256;
void frame(array<unsigned char,W>&t,string pc,vector<int> regs,vector<int>spares,int gap,int shift=0){
 t.fill(0); constexpr int physical[9]={6,2,0,4,3,7,8,5,1};
 vector<int> v(9);for(int i=0;i<9;i++)v[physical[i]]=regs[i];v.insert(v.end(),spares.begin(),spares.end());
 t[OFF-1-shift]=1;t[OFF+56+gap-shift]=1;
 for(int i=0;i<(int)pc.size();i++)if(pc[i]=='1')t[OFF+i-shift]=1;
 int cursor=57+gap;for(int n:v){for(int j=1;j<=n+1;j++)t[OFF+cursor+j-shift]=1;cursor+=n+2;}
}
string strip(string pc,char b,int count){for(int i=(int)pc.size()-1;i>=0;i--)if(pc[i]==b&&--count==0)return pc.substr(0,i);return "";}
pair<string,int> inc(string pc){for(int i=(int)pc.size()-1;i>=0;i--){if(pc[i]=='0'){pc[i]='1';return {pc,0};}pc[i]='0';}return {pc,1};}
extern "C" int check(const int*table,const char*src,int max_cases,int variants,long long*steps){
 istringstream in(src);vector<Site> sites;Site st;while(in>>st.p>>st.op>>st.a)sites.push_back(st);
 int count=0;
 for(int idx=0;idx<(int)sites.size();idx++){
  const auto&s=sites[idx];
  for(int sample=0;sample<variants;sample++)for(int positive=0;positive<(s.op=="CD"?2:1);positive++){
   vector<int> regs(9),spares(sample+1);for(int i=0;i<9;i++)regs[i]=sample?(i*3+sample)%4:0;for(int i=0;i<(int)spares.size();i++)spares[i]=sample?(i+sample)%3:0;
   if(s.op=="CD")regs[s.a]=positive?sample+1:0;
   int gap=sample?sample:0,shift=0,delta=0;array<unsigned char,W>t,e;frame(t,s.p,regs,spares,gap);string pc=s.p;
   if(s.op=="CI"){regs[s.a]++;spares.push_back(1);auto x=inc(pc);pc=x.first;shift=x.second;}
   else if(s.op=="CD"&&positive){regs[s.a]--;delta=1;auto x=inc(pc);pc=x.first;shift=x.second;}
   else if(s.op=="CD"||s.op=="CB"){auto x=inc(strip(pc,'0',s.op=="CD"?1:s.a));pc=x.first;shift=x.second;}
   else if(s.op=="CC")pc=strip(pc,'1',s.a);
   frame(e,pc,regs,spares,gap+delta+shift,shift);
   int q=84,h=OFF,tick=0;
   for(;tick<100000;tick++){
    if(tick&&((s.op=="CH"&&q==254)||(s.op!="CH"&&q==84&&h==OFF-shift&&t==e)))break;
    if(q==254||q<0||q>=1000||h<1||h>=W-1)return 1000000+idx;
    int k=6*q+3*t[h];t[h]=table[k];h+=table[k+1];q=table[k+2];
   }
   *steps+=tick;if(tick==100000)return idx+1;
   if(++count==max_cases)return 0;
  }
 }
 return 0;
}
