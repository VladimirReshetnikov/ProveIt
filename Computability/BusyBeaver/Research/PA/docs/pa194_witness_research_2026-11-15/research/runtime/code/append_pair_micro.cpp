#include <bits/stdc++.h>
using namespace std;struct A{int w,d,n;};
int main(int argc,char**argv){if(argc<2)return 2;array<A,2>rs[3000];bool ex[3000]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=1;rs[q][b]={w,d=='R'?1:-1,n};}
 vector<A>actions;for(int q:qs)for(int w:{0,1})for(int d:{-1,1})actions.push_back({w,d,q});
 long long trials=0,steps=0,screen=0,hits=0;
 auto run=[&](int left)->int{int tape=left;int q=66,h=0;
  // Local positions -5..12. Bit4 (position -1) is the new delimiter0.
  for(int st=0;st<160;st++){
   if(st&&q==40&&h>=0&&h<=8){int r=tape>>5,k=0;while(r&1){k++;r>>=1;}if(r==0&&k>=3&&k<=9&&(tape&31)==left)return k-1;}
   if(h<-5||h>12||!ex[q])return -1;int bit=tape>>(h+5)&1;auto a=rs[q][bit];tape=(tape&~(1<<(h+5)))|(a.w<<(h+5));h+=a.d;q=a.n;steps++;
  }return -1;};
 for(A a:actions){rs[66][0]=a;for(A b:actions){rs[198][0]=b;trials++;int k=run(8);if(k<2)continue;screen++;bool ok=true;for(int l=0;l<16;l++)if(run(l)!=k){ok=false;break;}if(ok){hits++;cout<<"{\"66,0\":["<<a.w<<','<<a.d<<','<<a.n<<"],\"198,0\":["<<b.w<<','<<b.d<<','<<b.n<<"],\"append\":"<<k<<"}"<<endl;}}}
 cerr<<"DONE trials "<<trials<<" first_pass "<<screen<<" hits "<<hits<<" steps "<<steps<<endl;
}
