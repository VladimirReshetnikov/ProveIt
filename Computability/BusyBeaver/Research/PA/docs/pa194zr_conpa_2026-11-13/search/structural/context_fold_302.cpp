#include <bits/stdc++.h>
using namespace std;
struct Act{int w,d,n;};
int main(int argc,char**argv){
 ifstream f(argv[1]);map<int,int>ix;vector<tuple<int,int,int,char,int>>raw;int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){raw.emplace_back(q,b,w,d,n);ix[q]=0;ix[n]=0;}
 vector<int>labs;for(auto&[k,v]:ix){v=labs.size();labs.push_back(k);}int N=labs.size(),R=argc>2?atoi(argv[2]):3,W=2*R+1,mask=(1<<W)-1;vector<array<Act,2>>tr(N);vector<bool>has(N);
 for(auto[q,b,w,d,n]:raw){has[ix[q]]=true;tr[ix[q]][b]={w,d=='R'?1:-1,ix[n]};}
 vector<vector<bool>>seen(N,vector<bool>(1<<W));deque<pair<int,int>>dq;int start=ix[74];seen[start][0]=true;dq.push_back({start,0});
 while(dq.size()){auto[q,x]=dq.front();dq.pop_front();if(!has[q])continue;Act a=tr[q][x>>R&1];int y=(x&~(1<<R))|(a.w<<R);int yy=a.d==1?y>>1:(y<<1)&mask;for(int fresh:{0,1}){int z=yy|(fresh<<(a.d==1?W-1:0));if(!seen[a.n][z]){seen[a.n][z]=true;dq.push_back({a.n,z});}}}
 vector<array<vector<int>,2>>contexts(N);int total=0;for(int q=0;q<N;q++)for(int x=0;x<=mask;x++)if(seen[q][x]){contexts[q][x>>R&1].push_back(x);total++;}cerr<<"radius "<<R<<" contexts "<<total<<" states "<<N<<"\n";
 long long attempts=0;int found=0,skipped=0;
 for(int a=0;a<N;a++)if(has[a]&&a!=start)for(int bb=a+1;bb<N;bb++)if(has[bb]&&bb!=start&&(labs[a]==302||labs[bb]==302)){
  auto proj=[&](int x){return x==a?bb:x;};
  auto sim=[&](int orig,int x,array<Act,2>cand,int known){int cur=bb,pos=0,tape=x;Act want=tr[orig][x>>R&1];want.n=proj(want.n);int wantbits=(x&~(1<<R))|(want.w<<R);int qs[64],ps[64],xs[64];
    for(int step=0;step<64;step++){
      if(step&&cur==want.n&&pos==want.d&&tape==wantbits)return 1;
      if(pos< -R||pos>R||!has[cur])return 0;
      for(int k=0;k<step;k++)if(qs[k]==cur&&ps[k]==pos&&xs[k]==tape)return 0;
      qs[step]=cur;ps[step]=pos;xs[step]=tape;
      int cell=R+pos,read=tape>>cell&1;if(cur==bb&&!(known&(1<<read)))return 2;
      Act act=cur==bb?cand[read]:tr[cur][read];act.n=proj(act.n);tape=(tape&~(1<<cell))|(act.w<<cell);pos+=act.d;cur=act.n;
    }return 0;};
  auto check=[&](int bit,array<Act,2>cand,int known){for(int orig:{a,bb})for(int x:contexts[orig][bit])if(!sim(orig,x,cand,known))return false;return true;};
  vector<Act>possible[2];
  for(int bit:{0,1})for(int ww:{0,1})for(int dd:{-1,1})for(int nn=0;nn<N;nn++)if(nn!=a){array<Act,2>cand;cand[bit]={ww,dd,nn};attempts++;if(check(bit,cand,1<<bit))possible[bit].push_back(cand[bit]);}
  if(possible[0].empty()||possible[1].empty())continue;
  long long combos=possible[0].size()*possible[1].size();if(combos>100000){skipped++;cerr<<"many "<<labs[a]<<" "<<labs[bb]<<" "<<possible[0].size()<<" "<<possible[1].size()<<"\n";continue;}
  for(auto x:possible[0])for(auto y:possible[1]){array<Act,2>cand={x,y};bool good=true;for(int orig:{a,bb})for(int bit:{0,1})for(int tape:contexts[orig][bit])if(sim(orig,tape,cand,3)!=1){good=false;break;}if(good){cout<<labs[a]<<" "<<labs[bb]<<" : "<<x.w<<" "<<x.d<<" "<<labs[x.n]<<" ; "<<y.w<<" "<<y.d<<" "<<labs[y.n]<<"\n";cout.flush();found++;}}
 }
 cerr<<"done attempts="<<attempts<<" found="<<found<<" skipped="<<skipped<<"\n";
}
