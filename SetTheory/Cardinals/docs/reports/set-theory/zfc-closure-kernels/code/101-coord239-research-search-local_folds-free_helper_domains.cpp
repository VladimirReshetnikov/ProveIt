#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,z;};struct Conf{int q,h,t;};
Row tab[256][2];bool exists_[256];vector<int> states,invs[256];
int L=4,R=4,W,N,F,maxnew=33,maxold=33;
struct Case{int input,t;vector<Conf> goals;};vector<Case> cases[2];
int retained,deleted;long long contexttests=0;
inline int mapped(int q){return q==deleted?retained:q;}

int helperq=-1,helperb;Row helperrow;vector<int>failededges;int failedindex=0;
bool testcase(Case const&c,int entry,Row rt[2],bool savefail=false){
 contexttests++;int x=c.t,pos=0,s=entry;bool yes=false;vector<int>used;
 for(int tt=0;tt<maxnew;++tt){
  if(pos < -L||pos>R||s==254)break;
  int bb=(x>>(L+pos))&1;Row a;
  if(s==retained)a=rt[bb];
  else {if(savefail)used.push_back(2*s+bb);a=helperq==s&&helperb==bb?helperrow:tab[s][bb];}
  x=(x&~(1<<(L+pos)))|(a.w<<(L+pos));pos+=a.d;s=mapped(a.z);
  for(auto const&g:c.goals)if(s==mapped(g.q)&&pos==g.h&&x==g.t){yes=true;break;}
  if(yes)break;
 }
 if(!yes&&savefail){sort(used.begin(),used.end());used.erase(unique(used.begin(),used.end()),used.end());failededges=move(used);}
 return yes;
}
bool testcases(vector<Case>const&cs,int entry,Row rt[2],bool savefail=false){
 for(int i=0;i<int(cs.size());i++)if(!testcase(cs[i],entry,rt,savefail)){failedindex=i;return false;}
 return true;
}
int main(int argc,char**argv){
 if(argc<2)return 2;
 if(argc>2)L=stoi(argv[2]);if(argc>3)R=stoi(argv[3]);if(argc>4)maxold=stoi(argv[4]);if(argc>5)maxnew=stoi(argv[5]);
 W=L+R+1;N=1<<W;F=N-1;
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};exists_[q]=true;}
 for(int q=0;q<256;++q)if(exists_[q])states.push_back(q);
 vector<vector<bool>>seen(256,vector<bool>(N));queue<pair<int,int>>todo;
 for(int m=0;m<N;++m){seen[95][m]=true;todo.push({95,m});}
 while(!todo.empty()){
  auto[q,m]=todo.front();todo.pop();invs[q].push_back(m);if(q==254)continue;
  Row a=tab[q][(m>>L)&1];int x=(m&~(1<<L))|(a.w<<L);int ys[2];
  if(a.d==1){ys[0]=x>>1;ys[1]=ys[0]|(1<<(W-1));}else{ys[0]=(x<<1)&F;ys[1]=ys[0]|1;}
  for(int y:ys)if(!seen[a.z][y]){seen[a.z][y]=true;todo.push({a.z,y});}
 }
 if(argc>6){for(auto &v:invs)v.clear();ifstream dd(argv[6]);int q,m;while(dd>>q>>m)invs[q].push_back(m);}
 vector<Case>pre[256][2];long long contexts=0;
 for(int q:states){
  sort(invs[q].begin(),invs[q].end(),[](int a,int b){return ((a*101)&F)<((b*101)&F);});
  for(int m:invs[q]){int b=(m>>L)&1;Case c{q,m,{}};int h=0,t=m,s=q;
   for(int k=0;k<maxold;k++){
    if(s==254||h<-L||h>R)break;
    int bit=(t>>(L+h))&1;Row a=tab[s][bit];t=(t&~(1<<(L+h)))|(a.w<<(L+h));s=a.z;h+=a.d;c.goals.push_back({s,h,t});
   }
   pre[q][b].push_back(move(c));contexts++;
  }
 }
 cerr<<"Searching L="<<L<<" R="<<R<<" maxold="<<maxold<<" maxnew="<<maxnew<<" contexts="<<contexts<<endl;
 long long paircount=0,checked=0,candidate=0,partials=0;auto start=chrono::steady_clock::now();

 long long helpchecked=0;
 for(int p:states)for(int q:states)if(p<q){
  int common=-1;
  for(int b=0;b<2;b++)if(tab[p][b].w==tab[q][b].w&&tab[p][b].d==tab[q][b].d&&tab[p][b].z==tab[q][b].z)common=b;
  if(common<0)continue;
  retained=p;deleted=q;int differing=1-common;
  for(int b=0;b<2;++b){cases[b].clear();for(int s:{p,q})cases[b].insert(cases[b].end(),pre[s][b].begin(),pre[s][b].end());
   stable_sort(cases[b].begin(),cases[b].end(),[](auto const&a,auto const&b){return ((a.t*101)&F)<((b.t*101)&F);});
  }
  Row rows[2];rows[common]=tab[p][common];
  for(int w=0;w<2;++w)for(int d:{-1,1})for(int z:states)if(z!=deleted){
   rows[differing]={w,d,z};checked++;helperq=-1;
   if(testcases(cases[differing],retained,rows,true)){cout<<"BASE "<<p<<" "<<q<<endl;candidate++;continue;}
   vector<int>edges=failededges;Case const&witness=cases[differing][failedindex];
   for(int e:edges){
    helperq=e/2;helperb=e%2;
    if(helperq==p||helperq==q)continue;
    for(int hw=0;hw<2;hw++)for(int hd:{-1,1})for(int hz:states)if(hz!=deleted){
     if(hw==tab[helperq][helperb].w&&hd==tab[helperq][helperb].d&&hz==tab[helperq][helperb].z)continue;
     helperrow={hw,hd,hz};helpchecked++;
     if(!testcase(witness,retained,rows))continue;
     if(!testcases(pre[helperq][helperb],helperq,rows))continue;
     if(!testcases(cases[differing],retained,rows))continue;
     Row a=rows[0],b=rows[1];
     cout<<"HELPER "<<helperq<<" "<<helperb<<" "<<hw<<" "<<hd<<" "<<hz<<" FOLD "<<p<<" "<<q<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;candidate++;
    }
   }
  }
  paircount++;
  if(paircount%10==0)cerr<<"pairs "<<paircount<<" last "<<p<<"/"<<q<<" checked "<<checked<<" helperchecks "<<helpchecked<<" found "<<candidate<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"FINISHED pairs "<<paircount<<" checked "<<checked<<" helperchecks "<<helpchecked<<" candidates "<<candidate<<" contexttests "<<contexttests<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
