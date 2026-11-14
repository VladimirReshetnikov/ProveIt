#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <random>
using namespace std;
struct Row {int w,d,z;};
struct Sample{uint64_t tape; int oldq,b;};
Row tm[512][2];vector<int> states;
int pi(int s,int q,int r){return s==q?r:s;}
bool trial(int q,int r,int b,Row a,Sample sample,int limit=31){
 uint64_t tape=sample.tape,expected=tape;int h=32,s=r;
 Row end=tm[sample.oldq][sample.b];int goalq=pi(end.z,q,r),goalh=32+end.d;
 expected=(expected&~(1ULL<<32))|((uint64_t)end.w<<32);
 for(int i=0;i<limit;i++){
  if(s==254||h<1||h>62)return false;
  int bit=(tape>>h)&1;Row row;
  if(s==r&&bit==b)row=a;else row=tm[s][bit];
  tape=(tape&~(1ULL<<h))|((uint64_t)row.w<<h);h+=row.d;s=pi(row.z,q,r);
  if(s==goalq&&h==goalh&&tape==expected)return true;
 }
 return false;
}
int main(int argc,char**argv){
 ifstream f(argv[1]);string s;bool active[512]={};
 while(getline(f,s)){if(s.empty()||s[0]=='#')continue;stringstream ss(s);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;tm[q][b]={w,d=='R'?1:-1,z};active[q]=true;}
 for(int q=1;q<512;q++)if(active[q])states.push_back(q);
 int rwindow=stoi(argv[3]),bits=2*rwindow+1,count=1<<bits;
 vector<unsigned char> seen(512*count);ifstream win(argv[2],ios::binary);win.read((char*)seen.data(),seen.size());
 mt19937_64 rng(88270);vector<Sample> samples[512][2];
 for(int q:states)for(int b=0;b<2;b++){
  vector<int> poss;for(int x=0;x<count;x++)if(seen[q*count+x]&&(((x>>rwindow)&1)==b))poss.push_back(x);
  if(poss.empty())continue;
  shuffle(poss.begin(),poss.end(),rng);
  for(int k=0;k<min(12,(int)poss.size());k++){
   uint64_t tape=rng(),mask=((1ULL<<bits)-1)<<(32-rwindow);
   tape=(tape&~mask)|((uint64_t)poss[k]<<(32-rwindow));samples[q][b].push_back({tape,q,b});
  }
 }
 int pairs=0;
 for(int q:states)for(int r:states){if(q==r)continue;pairs++;
  for(int b=0;b<2;b++){Row x=tm[q][1-b],y=tm[r][1-b];if(x.w!=y.w||x.d!=y.d||pi(x.z,q,r)!=pi(y.z,q,r))continue;for(int helper:states){if(helper==q)continue;
   for(int d:{-1,1})for(int w:{0,1}){
    Row a{w,d,helper};bool ok=true;
    for(int bit:{b,1-b}){for(int oldq:{q,r}){for(Sample sp:samples[oldq][bit])if(!trial(q,r,b,a,sp)){ok=false;break;}if(!ok)break;}if(!ok)break;}
    if(ok)cout<<q<<' '<<r<<' '<<b<<' '<<w<<' '<<d<<' '<<helper<<endl;
   }
  }
 }
 }
 cerr<<"pairs "<<pairs<<endl;
}
