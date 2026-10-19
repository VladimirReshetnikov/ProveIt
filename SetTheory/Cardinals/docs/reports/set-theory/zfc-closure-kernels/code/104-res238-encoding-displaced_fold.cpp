#include <bits/stdc++.h>
using namespace std;
struct Row {int w,d,z;}; struct Goal {int x,h,q;}; struct Case {int source,x;vector<Goal>g;};
#ifndef RADIUS
#define RADIUS 5
#endif
constexpr int R=RADIUS,W=2*R+1,SIZE=1<<W,MASK=SIZE-1;
Row O[256][2],N[256][2]; bool present[256]; vector<int> states,inv[256]; vector<Case> pre[256];
int del_,ret_,shift_,oldlim=63,newlim=127;long long actions=0;
int mapped(int q){return q==del_?ret_:q;}int dh(int q){return q==del_?shift_:0;}
bool check(Case const&c,Row const rr[2],int partial=-1){
 int q=mapped(c.source),x=c.x,h=dh(c.source);
 for(int n=0;n<newlim;n++){
  if(q==254||h < -R||h>R)return false;
  int b=(x>>(R+h))&1;
  if(q==ret_&&partial>=0&&b!=partial)return true;
  Row a=q==ret_?rr[b]:N[q][b];
  x=(x&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;q=a.z;
  for(auto const&g:c.g)if(q==mapped(g.q)&&h==g.h+dh(g.q)&&x==g.x)return true;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc<2)return 2; if(argc>2)oldlim=atoi(argv[2]);if(argc>3)newlim=atoi(argv[3]);
 ifstream f(argv[1]);string line;while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;O[q][b]={w,d=='R'?1:-1,z};present[q]=1;}
 for(int q=0;q<256;q++)if(present[q])states.push_back(q);
 static bool seen[256][SIZE];queue<pair<int,int>>todo;
 for(int x=0;x<SIZE;x++){seen[95][x]=1;todo.push({95,x});}
 while(!todo.empty()){auto[q,m]=todo.front();todo.pop();inv[q].push_back(m);if(q==254)continue;auto a=O[q][(m>>R)&1];int x=(m&~(1<<R))|(a.w<<R),ys[2];if(a.d==1){ys[0]=x>>1;ys[1]=ys[0]|(1<<(W-1));}else{ys[0]=(x<<1)&MASK;ys[1]=ys[0]|1;}for(int y:ys)if(!seen[a.z][y]){seen[a.z][y]=1;todo.push({a.z,y});}}
 if(char const*df=getenv("SYNTH_DOMAINS")){for(int q=0;q<256;q++)inv[q].clear();ifstream in(df);int q,m;while(in>>q>>m){if(q<0||q>255||m<0||m>=SIZE)return 2;inv[q].push_back(m);}}
 for(int s:states)for(int m:inv[s]){Case c{s,m,{}};int q=s,x=m,h=0;for(int i=0;i<oldlim;i++){if(q==254||h < -R||h>R)break;auto a=O[q][(x>>(R+h))&1];x=(x&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;q=a.z;c.g.push_back({x,h,q});}pre[s].push_back(move(c));}
 for(int s:states)stable_sort(pre[s].begin(),pre[s].end(),[](auto const&a,auto const&b){return ((a.x*101)&MASK)<((b.x*101)&MASK);});
 vector<int> targets=states;targets.push_back(254);long long pairs=0,found=0;auto start=chrono::steady_clock::now();
 for(int q:states){if(q==95)continue;set<int> dirs;bool self=false;for(int s:states)for(int b=0;b<2;b++)if(O[s][b].z==q){dirs.insert(O[s][b].d);if(s==q)self=true;}if(self||dirs.size()!=1)continue;del_=q;shift_=-2*(*dirs.begin());
  for(int p:states)if(p!=q){ret_=p;
   for(int s:states)if(s!=q)for(int b=0;b<2;b++){N[s][b]=O[s][b];if(N[s][b].z==q){N[s][b].z=p;N[s][b].d=-N[s][b].d;}}
   vector<Case const*> cs[2];for(int s:{p,q})for(auto const&c:pre[s])cs[(c.x>>(R+dh(s)))&1].push_back(&c);
   vector<Row> good[2];Row rr[2];
   for(int b=0;b<2;b++){
    for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:targets)if(z!=q){rr[b]={w,d,z};actions++;bool ok=true;for(auto cp:cs[b])if(!check(*cp,rr,b)){ok=false;break;}if(ok)good[b].push_back(rr[b]);}
    if(good[b].empty())break;
   }
   for(auto a:good[0])for(auto b:good[1]){rr[0]=a;rr[1]=b;bool ok=true;for(int bit=0;bit<2;bit++)for(auto cp:cs[bit])if(ok&&!check(*cp,rr)){ok=false;break;}if(ok){cout<<"SOLUTION delete "<<q<<" retain "<<p<<" shift "<<shift_<<" rows "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;found++;}}
   if(++pairs%1000==0)cerr<<"pairs "<<pairs<<" actions "<<actions<<" found "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
  }
 }
 cerr<<"FINISHED radius "<<R<<" old "<<oldlim<<" new "<<newlim<<" pairs "<<pairs<<" actions "<<actions<<" found "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
