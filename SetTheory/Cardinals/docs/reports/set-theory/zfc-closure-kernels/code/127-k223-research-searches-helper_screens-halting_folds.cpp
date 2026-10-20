#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,z;};struct Conf{int q,h,t;};
Row tab[1024][2];bool exists_[2048];vector<int> states,invs[2048];
int L=4,R=4,W,N,F,maxnew=33,maxold=33,startq=-1;
struct Case{int input,t;vector<Conf> goals;};vector<Case> cases[2];
int retained,deleted;long long contexttests=0;
inline int mapped(int q){return q==deleted?retained:q;}

struct Patch{int q,b;Row a;};vector<Patch>patches;vector<int>byedge[2048];
vector<int>failededges;
bool testcases(vector<Case>const&cs,int entry,int input,Row rt[2],bool complete,int pi=-1,bool savefail=false){
 for(auto const&c:cs){
  contexttests++;int x=c.t,pos=0,s=entry;bool yes=false;vector<int>used;
  for(int tt=0;tt<maxnew;++tt){
   if(pos < -L||pos>R||s==254)break;
   int bb=(x>>(L+pos))&1;
   if(s==retained&&bb!=input&&!complete){yes=true;break;}
   Row a;
   if(s==retained)a=rt[bb];
   else {if(savefail)used.push_back(2*s+bb);a=pi>=0&&patches[pi].q==s&&patches[pi].b==bb?patches[pi].a:tab[s][bb];}
   x=(x&~(1<<(L+pos)))|(a.w<<(L+pos));pos+=a.d;s=mapped(a.z);
   for(auto const&g:c.goals)if((s==254&&g.q==254)||(s==mapped(g.q)&&pos==g.h&&x==g.t)){yes=true;break;}
   if(yes)break;
  }
  if(!yes){if(savefail){sort(used.begin(),used.end());used.erase(unique(used.begin(),used.end()),used.end());failededges=move(used);}return false;}
 }
 return true;
}
bool test(int b,Row rt[2],bool complete,int pi=-1,bool savefail=false){return testcases(cases[b],retained,b,rt,complete,pi,savefail);}
int main(int argc,char**argv){
 if(argc<2){cerr<<"Usage: all_tape_folds TABLE [radius] [fuel]\n";return 2;}
 if(argc>2)L=R=stoi(argv[2]); if(argc>3)maxold=maxnew=stoi(argv[3]);
 if(L<1||L>8)throw runtime_error("window radius range"); W=L+R+1;N=1<<W;F=N-1;
 ifstream f(argv[1]);if(!f)throw runtime_error("table file not found");string line;
 while(getline(f,line)){if(line.rfind("#! start ",0)==0){startq=stoi(line.substr(9));continue;} if(line.empty()||line[0]=='#')continue;stringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;if(q<0||q>=1024||z<0||z>=1024||b<0||b>1)throw runtime_error("label range");tab[q][b]={w,d=='R'?1:-1,z};exists_[q]=true;}
 for(int q=0;q<1024;++q)if(exists_[q])states.push_back(q);
 if(startq<0||!exists_[startq]||exists_[254])throw runtime_error("start/halt validation");
 vector<vector<bool>>seen(1024,vector<bool>(N));queue<pair<int,int>>todo;
 for(int m=0;m<N;++m){seen[startq][m]=true;todo.push({startq,m});}
 while(!todo.empty()){
  auto[q,m]=todo.front();todo.pop();invs[q].push_back(m);if(q==254)continue;
  Row a=tab[q][(m>>L)&1];int x=(m&~(1<<L))|(a.w<<L);int ys[2];
  if(a.d==1){ys[0]=x>>1;ys[1]=ys[0]|(1<<(W-1));}else{ys[0]=(x<<1)&F;ys[1]=ys[0]|1;}
  for(int y:ys)if(!seen[a.z][y]){seen[a.z][y]=true;todo.push({a.z,y});}
 }
 if(argc>4){
 vector<vector<int>> source(1024); ifstream fd(argv[4]); if(!fd)throw runtime_error("source domain input missing"); int q,m;
 while(fd>>q>>m){if(q<0||q>=1024||!exists_[q]||m<0||m>=N)throw runtime_error("source domain malformed");source[q].push_back(m);}
 for(int q:states){sort(source[q].begin(),source[q].end());sort(invs[q].begin(),invs[q].end());vector<int> both;set_intersection(source[q].begin(),source[q].end(),invs[q].begin(),invs[q].end(),back_inserter(both));invs[q]=move(both);}
 }
 vector<Case>pre[1024][2];long long contexts=0;
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


 for(int p:states)for(int q:states)if(p<q){
  retained=p;deleted=q;
  for(int b=0;b<2;++b){cases[b].clear();for(int s:{p,q})cases[b].insert(cases[b].end(),pre[s][b].begin(),pre[s][b].end());}
  Row rows[2];vector<Row>ok[2];vector<int> targets=states;targets.push_back(254);
  for(int b=0;b<2;++b)for(int w=0;w<2;++w)for(int d:{-1,1})for(int z:targets)if(z!=deleted){
   rows[b]={w,d,z};checked++;
   if(test(b,rows,false))ok[b].push_back(rows[b]);
  }
  for(auto a:ok[0])for(auto b:ok[1]){
   rows[0]=a;rows[1]=b;
   if(!test(0,rows,true)||!test(1,rows,true))continue;
   cout<<"BASE "<<p<<" "<<q<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;candidate++;
  }
  if(++paircount%5000==0)cerr<<"pairs "<<paircount<<" found "<<candidate<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"FINISHED pairs "<<paircount<<" rowchecks "<<checked<<" candidates "<<candidate<<" contexts "<<contexttests<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
