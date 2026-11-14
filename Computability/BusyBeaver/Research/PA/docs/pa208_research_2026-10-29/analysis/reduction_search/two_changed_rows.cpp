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
bool trial(int q,int r,int b,Row a,int helper,int helperbit,Row second,Sample sample,int limit=31){
 uint64_t tape=sample.tape,expected=tape;int h=32,s=pi(sample.oldq,q,r);
 Row end=tm[sample.oldq][sample.b];int goalq=pi(end.z,q,r),goalh=32+end.d;
 expected=(expected&~(1ULL<<32))|((uint64_t)end.w<<32);
 for(int i=0;i<limit;i++){
  if(s==254||h<1||h>62)return false;
  int bit=(tape>>h)&1;Row row;
  if(s==r&&bit==b)row=a;else if(s==helper&&bit==helperbit)row=second;else row=tm[s][bit];
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
 int pairs=0;long long scans=0;
 for(int iq=0;iq<(int)states.size();iq++){int q=states[iq];for(int ir=0;ir<iq;ir++){int r=states[ir];
  for(int b=0;b<2;b++){
   Row oq=tm[q][b],orr=tm[r][b],oqother=tm[q][1-b],orother=tm[r][1-b];
   if(oqother.w!=orother.w||oqother.d!=orother.d||oqother.z!=orother.z)continue;
   if(oq.w!=b||orr.w!=b||oq.d!=1||orr.d!=1)continue;pairs++;
   for(int helper:states){if(helper==q||helper==r)continue;Row a{b,-1,helper};
    for(int helperbit=0;helperbit<2;helperbit++)for(int z:states){if(z==q)continue;
     for(int d:{-1,1})for(int w:{0,1}){Row second{w,d,z};scans++;bool ok=true;
      for(int oldq:{q,r}){for(Sample sp:samples[oldq][b])if(!trial(q,r,b,a,helper,helperbit,second,sp)){ok=false;break;}if(!ok)break;}
      if(!ok)continue;
      for(Sample sp:samples[helper][helperbit])if(!trial(q,r,b,a,helper,helperbit,second,sp)){ok=false;break;}
      if(ok)cout<<q<<' '<<r<<' '<<b<<' '<<helper<<' '<<helperbit<<' '<<w<<' '<<d<<' '<<z<<endl;
     }
    }
   }
  }
 }}
 cerr<<"pairs "<<pairs<<" scans "<<scans<<endl;
}
