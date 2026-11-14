#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Row{int w,d,z;};struct Sample{__uint128_t tape;int q,b;};struct Fold{int drop,keep,bit;};
Row tm[512][2];vector<int>states;vector<Sample>samples[512][2];constexpr int helper=500;
int pi(int q,Fold a,Fold b){if(q==a.drop)q=a.keep;if(q==b.drop)q=b.keep;return q;}
bool eq(Row a,Row b){return a.w==b.w&&a.d==b.d&&a.z==b.z;}
bool trial(Fold a,Fold b,int x0,int x1,int w0,int w1,Sample sp,int limit){
 __uint128_t tape=sp.tape,expected=tape;int h=64,q=pi(sp.q,a,b);Row goal=tm[sp.q][sp.b];
 expected=(expected&~((__uint128_t)1<<64))|((__uint128_t)goal.w<<64);
 for(int tick=0;tick<limit;++tick){
  if(q==254||h<0||h>127)return false;int read=(tape>>h)&1;Row step;
  if(q==helper)step={read?w1:w0,1,read?x1:x0};
  else if((q==a.keep&&read==a.bit)||(q==b.keep&&read==b.bit))step={read,-1,helper};
  else step=tm[q][read];
  tape=(tape&~((__uint128_t)1<<h))|((__uint128_t)step.w<<h);h+=step.d;q=pi(step.z,a,b);
  if(q==pi(goal.z,a,b)&&h==64+goal.d&&tape==expected)return true;
 }return false;
}
int main(int argc,char**argv){
 if(argc<6)return 2;ifstream f(argv[1]);string s;bool active[512]={};
 while(getline(f,s)){if(s.empty()||s[0]=='#')continue;istringstream ss(s);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;tm[q][b]={w,d=='R'?1:-1,z};active[q]=true;}
 for(int q=1;q<500;++q)if(active[q])states.push_back(q);
 int rad=stoi(argv[3]),bits=2*rad+1,count=1<<bits,limit=stoi(argv[5]);vector<unsigned char>seen(512*count);ifstream bin(argv[2],ios::binary);bin.read((char*)seen.data(),seen.size());
 mt19937_64 rng(8290731);for(int q:states)for(int b=0;b<2;++b){vector<int>poss;for(int x=0;x<count;++x)if(seen[q*count+x]&&(((x>>rad)&1)==b))poss.push_back(x);shuffle(poss.begin(),poss.end(),rng);
 for(int k=0;k<min(64,int(poss.size()));++k){__uint128_t t=((__uint128_t)rng()<<64)|rng(),mask=(((__uint128_t)1<<bits)-1)<<(64-rad);t=(t&~mask)|((__uint128_t)poss[k]<<(64-rad));samples[q][b].push_back({t,q,b});}}
 ifstream helpers(argv[4]);int x0,x1,w0,w1;Fold a;long long first=0,pairs=0,passed=0;
 while(helpers>>a.drop>>a.keep>>a.bit>>x0>>x1>>w0>>w1){++first;
 for(int u:states)if(u!=a.drop&&u!=a.keep)for(int v:states)if(u<v&&v!=a.drop&&v!=a.keep)for(int changed=0;changed<2;++changed){
 Row r=tm[u][changed],s=tm[v][changed],r1=tm[u][1-changed],s1=tm[v][1-changed];r1.z=pi(r1.z,a,{-1,-1,-1});s1.z=pi(s1.z,a,{-1,-1,-1});
 if((r1.w!=s1.w||r1.d!=s1.d||(r1.z!=s1.z&&!((r1.z==u||r1.z==v)&&(s1.z==u||s1.z==v))))||r.w!=changed||s.w!=changed||r.d!=1||s.d!=1)continue;
 for(int flip=0;flip<2;++flip){++pairs;Fold b={flip?u:v,flip?v:u,changed};bool ok=true;
 for(int oldq:{u,v,a.drop,a.keep}){for(int bit:{changed,1-changed}){for(auto sp:samples[oldq][bit])if(!trial(a,b,x0,x1,w0,w1,sp,limit)){ok=false;break;}if(!ok)break;}if(!ok)break;}
 if(ok){++passed;cout<<a.drop<<' '<<a.keep<<' '<<a.bit<<' '<<b.drop<<' '<<b.keep<<' '<<b.bit<<' '<<x0<<' '<<x1<<' '<<w0<<' '<<w1<<'\n';cout.flush();}
 }
 }
 }
 cerr<<"first_helpers "<<first<<" second_pair_orientations "<<pairs<<" passed "<<passed<<"\n";
}
