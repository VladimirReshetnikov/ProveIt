// Exploratory local contexts under a separately computed source invariant.
#include <string>
#include <vector>
#include <array>
#include <fstream>
#include <sstream>
#include <iostream>
using namespace std;
struct Site{string p,op;int a;};struct Tr{int w,d,q;};Tr tab[1000][2];
constexpr int W=4096,OFF=256;bool seen[1000][2048];long long steps=0,cases=0;
void frame(array<unsigned char,W>&t,string pc,vector<int> regs,vector<int>spares,int gap,int shift=0){
 t.fill(0);constexpr int physical[9]={6,2,0,4,3,7,8,5,1};vector<int>v(9);for(int i=0;i<9;i++)v[physical[i]]=regs[i];v.insert(v.end(),spares.begin(),spares.end());t[OFF-1-shift]=1;t[OFF+56+gap-shift]=1;
 for(int i=0;i<(int)pc.size();i++)if(pc[i]=='1')t[OFF+i-shift]=1;
 int cursor=57+gap;for(int n:v){for(int j=1;j<=n+1;j++)t[OFF+cursor+j-shift]=1;cursor+=n+2;}
}
string strip(string pc,char b,int count){for(int i=(int)pc.size()-1;i>=0;i--)if(pc[i]==b&&--count==0)return pc.substr(0,i);return "";}
pair<string,int> inc(string pc){for(int i=(int)pc.size()-1;i>=0;i--){if(pc[i]=='0'){pc[i]='1';return {pc,0};}pc[i]='0';}return {pc,1};}
void observe(int q,int h,const array<unsigned char,W>&t){int code=0;for(int j=-5;j<=5;j++)code|=int(t[h+j])<<(j+5);seen[q][code]=true;}
int main(int argc,char**argv){
 if(argc!=5)return 2;ifstream mi(argv[1]);string line;while(getline(mi,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream ss(line);ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};}
 ifstream si(argv[2]);vector<Site>sites;Site s;while(si>>s.p>>s.op>>s.a)sites.push_back(s);if(sites.size()!=3909)return 3;
 ifstream ai(argv[3]);int idx,mask;
 while(ai>>idx>>mask){const Site&s=sites[idx];
  for(int sample=0;sample<3;sample++){
   vector<int>regs(9),spares(sample+1,1);for(int j=0;j<9;j++)if(mask&(1<<j))regs[j]=sample<2?sample+1:1+((j*3+idx)%4);
   bool positive=s.op=="CD"&&regs[s.a]>0;int gap=sample==0?0:sample+2,shift=0,delta=0;array<unsigned char,W>t,e;frame(t,s.p,regs,spares,gap);string pc=s.p;
   if(s.op=="CI"){regs[s.a]++;spares.push_back(1);auto x=inc(pc);pc=x.first;shift=x.second;}
   else if(s.op=="CD"&&positive){regs[s.a]--;delta=1;auto x=inc(pc);pc=x.first;shift=x.second;}
   else if(s.op=="CD"||s.op=="CB"){auto x=inc(strip(pc,'0',s.op=="CD"?1:s.a));pc=x.first;shift=x.second;}
   else if(s.op=="CC")pc=strip(pc,'1',s.a);
   frame(e,pc,regs,spares,gap+delta+shift,shift);int q=84,h=OFF,tick=0;
   for(;tick<100000;tick++){
    if(tick&&((s.op=="CH"&&q==254)||(s.op!="CH"&&q==84&&h==OFF-shift&&t==e)))break;
    if(q==254||q<0||q>=1000||h<5||h>=W-5){cerr<<"error "<<idx<<endl;return 1;}
    observe(q,h,t);Tr a=tab[q][t[h]];t[h]=a.w;h+=a.d;q=a.q;
   }
   steps+=tick;cases++;if(tick==100000){cerr<<"limit "<<idx<<endl;return 1;}
  }
 }
 array<unsigned char,W>t{};int q=0,h=OFF;for(int i=0;i<48140;i++){observe(q,h,t);Tr a=tab[q][t[h]];t[h]=a.w;h+=a.d;q=a.q;}
 ofstream out(argv[4]);int count=0;for(int q=0;q<1000;q++)for(int code=0;code<2048;code++)if(seen[q][code]){count++;out<<q<<' '<<code<<'\n';}
 cout<<"PASS cases "<<cases<<" steps "<<steps<<" contexts "<<count<<endl;
}
