#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <chrono>
struct Action { int w,d,s; };
struct Case { int k,lo,hi;uint32_t tape; };
Action table[256][2];bool exists[256];
int run(const Case& c,int limit) {
 int q=6,h=0;uint32_t tape=c.tape;
 for(int tick=0;tick<=limit;tick++) {
  bool goal=c.k<8?(q==4&&h==-c.k-1):(q==84&&h>=-8&&h<=1);
  if(goal&&tape==c.tape)return 0;
  if(tick==limit)return 1;
  if(h<c.lo||h>c.hi)return 2;
  if(q<0||q>=256||!exists[q])return 3;
  uint32_t bit=1u<<(h+8);Action a=table[q][!!(tape&bit)];
  if(a.w)tape|=bit;else tape&=~bit;h+=a.d;q=a.s;
 }
 return 4;
}
int main(int argc,char**argv) {
 int limit=argc>2?atoi(argv[2]):1000;std::ifstream in(argv[1]);std::string line;
 while(std::getline(in,line)){if(line.empty()||line[0]=='#')continue;std::istringstream s(line);int q,b,w,dest;char d;s>>q>>b>>w>>d>>dest;table[q][b]={w,d=='R'?1:-1,dest};exists[q]=true;}
 exists[74]=false;
 std::vector<Action> acts;for(int s=0;s<256;s++)if(exists[s])for(int w=0;w<2;w++)for(int d:{-1,1})acts.push_back({w,d,s});
 std::vector<Case> cases;
 for(int k:{6,7}) {uint32_t tape=1u<<(8-k);int hi=k==6?12:13;for(int j=2;j<=hi;j++)tape|=1u<<(j+8);cases.push_back({k,-k,hi,tape});}
 for(int r=0;r<=10;r++){uint32_t tape=0;for(int j=2;j<3+r;j++)tape|=1u<<(j+8);cases.push_back({8,-8,3+r,tape});}
 uint64_t recipes=0,checks=0,reject[5]={},survivors=0;auto start=std::chrono::steady_clock::now();
 for(auto a:acts)for(auto b:acts){table[58][0]=a;table[58][1]=b;recipes++;bool ok=true;for(auto c:cases){checks++;int reason=run(c,limit);if(reason){reject[reason]++;ok=false;break;}}if(ok){survivors++;printf("SURVIVOR %d %c %d ; %d %c %d\n",a.w,a.d==1?'R':'L',a.s,b.w,b.d==1?'R':'L',b.s);fflush(stdout);}}
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();printf("{\"recipes\":%llu,\"case_checks\":%llu,\"survivors\":%llu,\"fuel\":%d,\"fuel_reject\":%llu,\"exterior_reject\":%llu,\"missing_reject\":%llu,\"seconds\":%.3f}\n",(unsigned long long)recipes,(unsigned long long)checks,(unsigned long long)survivors,limit,(unsigned long long)reject[1],(unsigned long long)reject[2],(unsigned long long)reject[3],sec);
}
