#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,z;bool operator==(Row const&a)const{return w==a.w&&d==a.d&&z==a.z;}};
struct Goal{int tape,h,q;};
struct Case{int source,tape;vector<Goal>goals;};
#ifndef RADIUS
#define RADIUS 4
#endif
#ifndef RELAXED_HALT
#define RELAXED_HALT 0
#endif
constexpr int R=RADIUS,W=2*R+1,SIZE=1<<W,MASK=SIZE-1;
Row O[256][2],N[256][2];bool present[256];vector<int>states,inv[256];
vector<Case>pre[256][2];int del_,ret_,oldlim=31,newlim=63;
inline int mapped(int q){return q==del_?ret_:q;}
bool check(Case const&c,vector<pair<int,int>>*trace=nullptr){
 int q=mapped(c.source),x=c.tape,h=0;
 for(int n=0;n<newlim;n++){
  if(q==254||h < -R||h>R)return false;
  int b=(x>>(R+h))&1;
  if(trace&&q!=ret_){pair<int,int>row{q,b};if(find(trace->begin(),trace->end(),row)==trace->end())trace->push_back(row);}
  Row a=N[q][b];x=(x&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;q=a.z;
  for(auto const&g:c.goals)if((q==mapped(g.q)&&h==g.h&&x==g.tape)||(RELAXED_HALT&&q==254&&g.q==254))return true;
 }
 return false;
}
Case const* failure(vector<Case>const&cs){for(auto const&c:cs)if(!check(c))return &c;return nullptr;}
int main(int argc,char**argv){
 if(argc<2){cerr<<"Usage helper_compensation TABLE [OLD_LIMIT NEW_LIMIT]\n";return 2;}
 if(argc>2)oldlim=atoi(argv[2]);if(argc>3)newlim=atoi(argv[3]);
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;O[q][b]={w,d=='R'?1:-1,z};present[q]=1;}
 for(int q=0;q<256;q++)if(present[q])states.push_back(q);
 static bool seen[256][SIZE];queue<pair<int,int>>todo;
 for(int m=0;m<SIZE;m++){seen[95][m]=1;todo.push({95,m});}
 while(!todo.empty()){
  auto[q,m]=todo.front();todo.pop();inv[q].push_back(m);if(q==254)continue;
  Row a=O[q][(m>>R)&1];int x=(m&~(1<<R))|(a.w<<R),ys[2];
  if(a.d==1){ys[0]=x>>1;ys[1]=ys[0]|(1<<(W-1));}else{ys[0]=(x<<1)&MASK;ys[1]=ys[0]|1;}
  for(int y:ys)if(!seen[a.z][y]){seen[a.z][y]=1;todo.push({a.z,y});}
 }
 if(char const*df=getenv("SYNTH_DOMAINS")){for(int q=0;q<256;q++)inv[q].clear();ifstream in(df);int q,m;while(in>>q>>m){if(q<0||q>255||m<0||m>=SIZE)return 2;inv[q].push_back(m);}}
 for(int s:states)for(int m:inv[s]){
  Case c{s,m,{}};int q=s,x=m,h=0;
  for(int i=0;i<oldlim;i++){
   if(q==254||h < -R||h>R)break;Row a=O[q][(x>>(R+h))&1];
   x=(x&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;q=a.z;c.goals.push_back({x,h,q});
  }
  pre[s][(m>>R)&1].push_back(move(c));
 }
 for(int s:states)for(int b=0;b<2;b++)stable_sort(pre[s][b].begin(),pre[s][b].end(),[](auto const&a,auto const&b){return ((a.tape*101)&MASK)<((b.tape*101)&MASK);});
 vector<int>targets=states;if(RELAXED_HALT)targets.push_back(254);
 long long pairs=0,overlays=0,actions=0,firstpass=0,helperpass=0,found=0;auto began=chrono::steady_clock::now();
 for(int p:states)for(int q:states)if(p<q){
  ret_=p;del_=q;
  for(int s:states)if(s!=del_)for(int b=0;b<2;b++){N[s][b]=O[s][b];N[s][b].z=mapped(N[s][b].z);}
  for(int ov=0;ov<4;ov++){
   overlays++;
   for(int b=0;b<2;b++){N[ret_][b]=O[(ov>>b)&1?del_:ret_][b];N[ret_][b].z=mapped(N[ret_][b].z);}
   Case const*bad=nullptr;
   for(int s:{ret_,del_})for(int b=0;b<2;b++)if(!bad)bad=failure(pre[s][b]);
   if(!bad){cout<<"OVERLAY "<<del_<<" "<<ret_<<" "<<ov<<endl;found++;continue;}
   vector<pair<int,int>>tr;check(*bad,&tr);
   // Every single helper-row repair must touch this first failing run.
   for(auto [hs,hb]:tr){
    Row saved=N[hs][hb];
    for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:targets)if(z!=del_){
     Row a{w,d,z};if(a==saved)continue;N[hs][hb]=a;actions++;
     if(!check(*bad))continue;firstpass++;
     if(failure(pre[hs][hb]))continue;helperpass++;
     bool okay=true;for(int s:{ret_,del_})for(int b=0;b<2;b++)if(okay&&failure(pre[s][b]))okay=false;
     if(okay){cout<<"SOLUTION "<<del_<<" "<<ret_<<" "<<ov<<" "<<hs<<" "<<hb<<" "<<w<<" "<<d<<" "<<z<<endl;found++;}
    }
    N[hs][hb]=saved;
   }
  }
  if(++pairs%1000==0)cerr<<"pairs "<<pairs<<" overlays "<<overlays<<" actions "<<actions<<" firstpass "<<firstpass<<" helperpass "<<helperpass<<" found "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;
 }
 cerr<<"FINISHED radius "<<R<<" old "<<oldlim<<" new "<<newlim<<" pairs "<<pairs<<" overlays "<<overlays<<" actions "<<actions<<" firstpass "<<firstpass<<" helperpass "<<helperpass<<" found "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;
 return 0;
}
