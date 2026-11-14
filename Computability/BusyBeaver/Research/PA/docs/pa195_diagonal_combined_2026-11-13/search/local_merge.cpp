#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;};
int main(int argc,char**argv){
 int r=argc>2?atoi(argv[2]):4, L=2*r+1, W=1<<L, mask=W-1;
 ifstream f(argv[1]);map<int,array<A,2>> raw;int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n)raw[q][b]={w,d=='R'?1:-1,n};
 vector<int> names;for(auto [q,a]:raw)names.push_back(q);int N=names.size();
 map<int,int> ids;for(int i=0;i<N;i++)ids[names[i]]=i;ids[254]=N;
 vector<array<A,2>> a(N);for(int i=0;i<N;i++)for(int b=0;b<2;b++){auto z=raw[names[i]][b];a[i][b]={z.w,z.d,ids.at(z.n)};}
 vector<vector<unsigned char>> seen(N+1,vector<unsigned char>(W));vector<vector<int>> ctx(N+1);queue<pair<int,int>> todo;
 auto add=[&](int q,int bits){if(!seen[q][bits]){seen[q][bits]=1;ctx[q].push_back(bits);if(q<N)todo.push({q,bits});}};
 if(argc>3&&string(argv[3])=="blank")add(ids.at(74),0);else for(int i=0;i<W;i++)add(ids.at(74),i);
 while(todo.size()){auto [q,bits]=todo.front();todo.pop();auto z=a[q][(bits>>r)&1];int v=(bits&~(1<<r))|(z.w<<r);if(z.d>0){v>>=1;add(z.n,v);add(z.n,v|(1<<(L-1)));}else {v=(v<<1)&mask;add(z.n,v);add(z.n,v|1);}}
 cerr<<"closure radius "<<r<<" states "<<N<<" contexts ";int total=0;for(auto &s:ctx)total+=s.size();cerr<<total<<"\n";
 for(int i=0;i<N;i++)if(ctx[i].size()<W/8)cerr<<names[i]<<":"<<ctx[i].size()<<" ";cerr<<"\n";
 int checked=0,passes=0;
 for(int rem=0;rem<N;rem++)if(names[rem]!=74){
  for(int keep=0;keep<N;keep++)if(keep!=rem){
   auto project=[&](int x){return x==rem?keep:x;};
   bool good=true;int maxt=0;
   for(int bits:ctx[rem]){
    A old=a[rem][(bits>>r)&1];int ebits=(bits&~(1<<r))|(old.w<<r),epos=old.d,eq=project(old.n);
    int v=bits,pos=0,cq=keep;bool success=false;
    for(int t=1;t<=63;t++){
     if(cq==N||abs(pos)>r)break;int at=pos+r;A z=a[cq][(v>>at)&1];v=(v&~(1<<at))|(z.w<<at);pos+=z.d;cq=project(z.n);
     if(v==ebits&&pos==epos&&cq==eq){success=true;maxt=max(maxt,t);break;}
    }
    if(!success){good=false;break;}
   }
   checked++;
   if(good){passes++;cout<<"MERGE "<<names[rem]<<" -> "<<names[keep]<<" duration "<<maxt<<" contexts "<<ctx[rem].size()<<"\n";}
  }
 }
 cerr<<"checked "<<checked<<" passes "<<passes<<"\n";
 int pairs=0,rowschecked=0;
 for(int rem=0;rem<N;rem++)if(names[rem]!=74)for(int keep=rem+1;keep<N;keep++)if(names[keep]!=74){
  auto project=[&](int x){return x==rem?keep:x;};
  vector<A> opts[2];
  for(int bit=0;bit<2;bit++){
   for(int nq=0;nq<=N;nq++)if(nq!=rem&&nq!=keep)for(int dd:{-1,1})for(int ww=0;ww<2;ww++){
    A act={ww,dd,nq};bool good=true;int maxt=0;
    for(int src:{rem,keep}){for(int bits:ctx[src])if(((bits>>r)&1)==bit){
     A old=a[src][bit];int ebits=(bits&~(1<<r))|(old.w<<r),epos=old.d,eq=project(old.n);
     int v=bits,pos=0,cq=keep;bool success=false;
     for(int t=1;t<=63;t++){
      if(cq==N||abs(pos)>r)break;int at=pos+r;A z=t==1?act:a[cq][(v>>at)&1];v=(v&~(1<<at))|(z.w<<at);pos+=z.d;cq=project(z.n);
      if(v==ebits&&pos==epos&&cq==eq){success=true;maxt=max(maxt,t);break;}
      if(cq==keep)break;
     }
     if(!success){good=false;break;}
    }if(!good)break;}
    rowschecked++;
    if(good)opts[bit].push_back(act);
   }
   if(opts[bit].empty())break;
  }
  pairs++;
  if(opts[0].size()&&opts[1].size()){
   cout<<"FOLD "<<names[rem]<<" -> "<<names[keep]<<" OPTIONS "<<opts[0].size()<<","<<opts[1].size()<<"\n";
   for(int bit=0;bit<2;bit++)for(auto z:opts[bit])cout<<bit<<":"<<z.w<<","<<z.d<<","<<(z.n==N?254:names[z.n])<<"\n";
  }
 }
 cerr<<"rowfold pairs "<<pairs<<" row candidates "<<rowschecked<<"\n";
}
