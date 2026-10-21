#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,z; bool operator==(const A&o)const{return w==o.w&&d==o.d&&z==o.z;}};
int main(int argc,char**argv){
 if(argc<2)return 1;ifstream f(argv[1]);string line;A T[400][2];bool present[400]={0};vector<int>Q;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};if(!present[q]){present[q]=true;Q.push_back(q);}}
 sort(Q.begin(),Q.end());constexpr int R=3;long long tried=0;int nh=0;
 for(int origq:Q)for(int origb=0;origb<2;origb++){
  A old=T[origq][origb];
  for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:Q){A a{w,d,z};if(a==old)continue;++tried;bool pass=true;int maxsteps=0;
   for(int stencil=0;stencil<128;stencil++){
    if(((stencil>>R)&1)!=origb)continue;int want=(stencil&~(1<<R))|(old.w<<R);int bits=stencil,q=origq,h=R,steps;
    for(steps=0;steps<32;steps++){
     if(steps>0&&q==old.z&&h==R+old.d&&bits==want)break;
     if(h<0||h>=7||!present[q]){pass=false;break;}
     int b=(bits>>h)&1;A act=(q==origq&&b==origb)?a:T[q][b];bits=(bits&~(1<<h))|(act.w<<h);q=act.z;h+=act.d;
    }
    if(steps>=32)pass=false;if(!pass)break;maxsteps=max(maxsteps,steps);
   }
   if(pass){++nh;cout<<origq<<" "<<origb<<" "<<w<<" "<<(d==1?'R':'L')<<" "<<z<<" "<<maxsteps<<"\n";}
  }
 }
 cerr<<"TRIED "<<tried<<" HITS "<<nh<<endl;
}
