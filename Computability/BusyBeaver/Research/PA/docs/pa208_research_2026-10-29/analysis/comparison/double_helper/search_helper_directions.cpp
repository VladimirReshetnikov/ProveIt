#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Row{int w,d,z;};struct Sample{__uint128_t tape;int q,b;};
Row tm[512][2];vector<int>states;vector<Sample>samples[512][2];
int tag[512][2];constexpr int helper=500;
int pi(int s,int drop,int keep){return s==drop?keep:s;}
bool trial(int drop,int keep,int bit,int x0,int x1,int w0,int w1,int d0,int d1,Sample sp,int limit){
 __uint128_t tape=sp.tape,expected=tape;int h=64,q=keep;Row goal=tm[sp.q][sp.b];
 expected=(expected&~((__uint128_t)1<<64))|((__uint128_t)goal.w<<64);
 for(int tick=0;tick<limit;++tick){
  if(q==254||h<0||h>127)return false;int b=(tape>>h)&1;Row a;
  if(q==helper)a={b?w1:w0,b?d1:d0,b?x1:x0};else if(q==keep&&b==bit)a={b,-1,helper};else a=tm[q][b];
  tape=(tape&~((__uint128_t)1<<h))|((__uint128_t)a.w<<h);h+=a.d;q=pi(a.z,drop,keep);
  if(q==pi(goal.z,drop,keep)&&h==64+goal.d&&tape==expected)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc<5)return 2;ifstream f(argv[1]);string s;bool active[512]={};
 while(getline(f,s)){if(s.empty()||s[0]=='#')continue;istringstream ss(s);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;tm[q][b]={w,d=='R'?1:-1,z};active[q]=true;}
 for(int q=1;q<500;++q)if(active[q])states.push_back(q);
 int rad=stoi(argv[3]),bits=2*rad+1,count=1<<bits,limit=stoi(argv[4]);vector<unsigned char>seen(512*count);ifstream bin(argv[2],ios::binary);bin.read((char*)seen.data(),seen.size());
 mt19937_64 rng(8290731);
 for(int q:states)for(int b=0;b<2;++b){vector<int>poss;int tags=0;for(int x=0;x<count;++x)if(seen[q*count+x]&&(((x>>rad)&1)==b)){poss.push_back(x);tags|=1<<((x>>(rad-1))&1);}tag[q][b]=tags==1?0:tags==2?1:-1;
  shuffle(poss.begin(),poss.end(),rng);for(int k=0;k<min(16,int(poss.size()));++k){__uint128_t t=((__uint128_t)rng()<<64)|rng(),mask=(((__uint128_t)1<<bits)-1)<<(64-rad);t=(t&~mask)|((__uint128_t)poss[k]<<(64-rad));samples[q][b].push_back({t,q,b});}
 }
 vector<int>donors=states;donors.insert(donors.begin(),0);donors.push_back(helper);
 long long pairs=0,scans=0,passed=0;
 bool tags_only=argc<6||stoi(argv[5]);
 for(int a:states)for(int b:states)if(a<b)for(int changed=0;changed<2;++changed){
  Row a0=tm[a][changed],b0=tm[b][changed],a1=tm[a][1-changed],b1=tm[b][1-changed];
  if(a0.w!=changed||b0.w!=changed||a0.d!=1||b0.d!=1)continue;
  if(a1.w!=b1.w||a1.d!=b1.d||(a1.z!=b1.z&&!((a1.z==a||a1.z==b)&&(b1.z==a||b1.z==b))))continue;
  if(tags_only&&(tag[a][changed]<0||tag[b][changed]<0||tag[a][changed]==tag[b][changed]))continue;
  for(int flip=0;flip<2;++flip){int drop=flip?a:b,keep=flip?b:a;++pairs;
   for(int x0:donors)if(x0!=drop)for(int x1:donors)if(x1!=drop)for(int w0=0;w0<2;++w0)for(int w1=0;w1<2;++w1)for(int d0:{-1,1})for(int d1:{-1,1}){++scans;bool ok=true;
    for(int bit:{changed,1-changed}){for(int oldq:{a,b}){for(auto sp:samples[oldq][bit])if(!trial(drop,keep,changed,x0,x1,w0,w1,d0,d1,sp,limit)){ok=false;break;}if(!ok)break;}if(!ok)break;}
    if(ok){++passed;cout<<drop<<' '<<keep<<' '<<changed<<' '<<x0<<' '<<x1<<' '<<w0<<' '<<w1<<' '<<d0<<' '<<d1<<'\n';cout.flush();}
   }
  }
 }
 cerr<<"pairs "<<pairs<<" helpers "<<scans<<" passed "<<passed<<" tags_only "<<tags_only<<"\n";
}
