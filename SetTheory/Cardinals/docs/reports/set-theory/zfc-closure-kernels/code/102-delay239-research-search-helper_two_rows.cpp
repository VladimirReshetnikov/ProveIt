// Reuse the table/window machinery and one-row search as a named, unused function.
#define main helper_one_row_main
#include "helper_compensation.cpp"
#undef main
#ifndef EXPAND_RETAINED
#define EXPAND_RETAINED 0
#endif

int helper_;
vector<Case const*> groups_[2];
int prefix_class(Case const&c){
 int q=mapped(c.source),x=c.tape,h=0;
 for(int n=0;n<newlim;n++){
  if(q==254||h < -R||h>R)return -1;
  int b=(x>>(R+h))&1;if(q==helper_)return b;
  Row a=N[q][b];x=(x&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;q=a.z;
  for(auto const&g:c.goals)if((q==mapped(g.q)&&h==g.h&&x==g.tape)||(RELAXED_HALT&&q==254&&g.q==254))return 2;
 }
 return -1;
}
bool synth_check(int input,Row rt[2],bool complete){
 for(auto const*cp:groups_[input]){
  auto const&c=*cp;int q=mapped(c.source),x=c.tape,h=0;bool yes=false;
  for(int n=0;n<newlim;n++){
   if(q==254||h < -R||h>R)return false;
   int b=(x>>(R+h))&1;
   if(q==helper_&&b!=input&&!complete){yes=true;break;}
   Row a=q==helper_?rt[b]:N[q][b];
   x=(x&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;q=a.z;
   for(auto const&g:c.goals)if((q==mapped(g.q)&&h==g.h&&x==g.tape)||(RELAXED_HALT&&q==254&&g.q==254)){yes=true;break;}
   if(yes)break;
  }
  if(!yes)return false;
 }
 return true;
}
bool retained_partial(int input,Row row){
 for(int s:{ret_,del_})for(auto const&c:pre[s][input]){
  int q=ret_,x=c.tape,h=0;bool yes=false;
  for(int n=0;n<newlim;n++){
   if(q==254||h < -R||h>R)return false;
   int b=(x>>(R+h))&1;
   if(q==ret_&&b!=input){yes=true;break;}
   Row a=q==ret_?row:N[q][b];
   x=(x&~(1<<(R+h)))|(a.w<<(R+h));h+=a.d;q=a.z;
   for(auto const&g:c.goals)if((q==mapped(g.q)&&h==g.h&&x==g.tape)||(RELAXED_HALT&&q==254&&g.q==254)){yes=true;break;}
   if(yes)break;
  }
  if(!yes)return false;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc<2){cerr<<"Usage helper_two_rows TABLE [OLD_LIMIT NEW_LIMIT]\n";return 2;}
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
 vector<int>targets=states;targets.push_back(254);
 long long pairs=0,overlays=0,helpertries=0,prefixpass=0,actions=0,partials=0,found=0,retained_actions=0;auto began=chrono::steady_clock::now();
 for(int p:states)for(int q:states)if(p<q){
  ret_=p;del_=q;
  for(int s:states)if(s!=del_)for(int b=0;b<2;b++){N[s][b]=O[s][b];N[s][b].z=mapped(N[s][b].z);}
  vector<array<Row,2>>overlays_list;
  for(int ov=0;ov<4;ov++){
   array<Row,2>rr;
   for(int b=0;b<2;b++){rr[b]=O[(ov>>b)&1?del_:ret_][b];rr[b].z=mapped(rr[b].z);}
   overlays_list.push_back(rr);
  }
  if(EXPAND_RETAINED){
   vector<Row>opts[2];
   for(int b=0;b<2;b++){
    for(auto rr:overlays_list)if(find(opts[b].begin(),opts[b].end(),rr[b])==opts[b].end())opts[b].push_back(rr[b]);
    for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:targets)if(z!=del_){
     Row row{w,d,z};retained_actions++;
     if(retained_partial(b,row)&&find(opts[b].begin(),opts[b].end(),row)==opts[b].end())opts[b].push_back(row);
    }
   }
   for(auto a:opts[0])for(auto b:opts[1]){
    array<Row,2>rr{a,b};bool known=false;for(auto const&existing:overlays_list)if(existing==rr){known=true;break;}
    if(!known)overlays_list.push_back(rr);
   }
  }
  for(int ov=0;ov<(int)overlays_list.size();ov++){
   overlays++;
   for(int b=0;b<2;b++)N[ret_][b]=overlays_list[ov][b];
   Case const*bad=nullptr;
   for(int s:{ret_,del_})for(int b=0;b<2;b++)if(!bad)bad=failure(pre[s][b]);
   if(!bad){cout<<"OVERLAY "<<del_<<" "<<ret_<<" "<<ov<<endl;found++;continue;}
   vector<pair<int,int>>tr;check(*bad,&tr);set<int>helpers;for(auto row:tr)helpers.insert(row.first);
   for(int hs:helpers){
    helper_=hs;helpertries++;groups_[0].clear();groups_[1].clear();bool okay=true;
    int bc=prefix_class(*bad);if(bc<0)continue;if(bc<2)groups_[bc].push_back(bad);
    for(int s:{ret_,del_})for(int b=0;b<2;b++)for(auto const&c:pre[s][b]){
     if(!okay)break;int pc=prefix_class(c);if(pc<0){okay=false;break;}if(pc<2)groups_[pc].push_back(&c);
    }
    if(!okay)continue;prefixpass++;
    for(int b=0;b<2;b++)for(auto const&c:pre[hs][b])groups_[b].push_back(&c);
    vector<Row>good[2];Row rt[2];
    for(int b=0;b<2;b++){
     for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:targets)if(z!=del_){
      rt[b]={w,d,z};actions++;if(synth_check(b,rt,false))good[b].push_back(rt[b]);
     }
     if(good[b].empty())break;
    }
    partials+=good[0].size()+good[1].size();
    for(auto a:good[0])for(auto b:good[1]){rt[0]=a;rt[1]=b;
     if(synth_check(0,rt,true)&&synth_check(1,rt,true)){
      auto r0=N[ret_][0],r1=N[ret_][1];
      cout<<"SOLUTION "<<del_<<" "<<ret_<<" "<<ov<<" "<<hs<<" retained "<<r0.w<<" "<<r0.d<<" "<<r0.z<<" "<<r1.w<<" "<<r1.d<<" "<<r1.z<<" helper "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;found++;
     }
    }
   }
  }
  if(++pairs%1000==0)cerr<<"pairs "<<pairs<<" overlays "<<overlays<<" helpertries "<<helpertries<<" prefixpass "<<prefixpass<<" actions "<<actions<<" partials "<<partials<<" found "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;
 }
 cerr<<"FINISHED radius "<<R<<" relaxed_halt "<<RELAXED_HALT<<" expanded_retained "<<EXPAND_RETAINED<<" old "<<oldlim<<" new "<<newlim<<" pairs "<<pairs<<" overlays "<<overlays<<" helpertries "<<helpertries<<" prefixpass "<<prefixpass<<" retained_actions "<<retained_actions<<" actions "<<actions<<" partials "<<partials<<" found "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;
}
