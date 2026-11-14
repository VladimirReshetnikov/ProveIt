// Frame and PC helpers adapted from the supplied U208 runtime checkers.
// See ../licenses for the retained source-lineage notices.
#include <string>
#include <vector>
#include <array>
#include <cstring>
#include <sstream>
using namespace std;
struct Site{string p,op;int a;};
constexpr int W=512,OFF=128;
void frame(array<unsigned char,W>&t,string pc,vector<int> regs,vector<int>spares,int gap,int shift=0){
 t.fill(0); constexpr int physical[9]={6,2,0,4,3,7,8,5,1};
 vector<int> v(9);for(int i=0;i<9;i++)v[physical[i]]=regs[i];v.insert(v.end(),spares.begin(),spares.end());
 t[OFF-1-shift]=1;t[OFF+56+gap-shift]=1;
 for(int i=0;i<(int)pc.size();i++)if(pc[i]=='1')t[OFF+i-shift]=1;
 int cursor=57+gap;for(int n:v){for(int j=1;j<=n+1;j++)t[OFF+cursor+j-shift]=1;cursor+=n+2;}
}
string strip(string pc,char b,int count){for(int i=(int)pc.size()-1;i>=0;i--)if(pc[i]==b&&--count==0)return pc.substr(0,i);return "";}
pair<string,int> inc(string pc){for(int i=(int)pc.size()-1;i>=0;i--){if(pc[i]=='0'){pc[i]='1';return {pc,0};}pc[i]='0';}return {pc,1};}
