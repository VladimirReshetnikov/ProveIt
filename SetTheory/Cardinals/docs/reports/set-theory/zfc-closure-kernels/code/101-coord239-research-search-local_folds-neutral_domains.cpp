#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,z;};struct Conf{int q,h,t;};
Row tab[256][2];bool exists_[256];vector<int> states,invs[256];
int L=4,R=4,W,N,F,maxnew=33,maxold=33;
struct Case{int input,t;vector<Conf> goals;};vector<Case> cases[2];
int retained,deleted;long long contexttests=0;
inline int mapped(int q){return q==deleted?retained:q;}
bool test(int input,Row rt[2],bool complete){
 for(auto const&c:cases[input]){
  contexttests++;int x=c.t,pos=0,s=retained;bool yes=false;
  for(int tt=0;tt<maxnew;++tt){
   if(pos < -L||pos>R||s==254)return false;
   int bb=(x>>(L+pos))&1;
   if(s==retained&&bb!=input&&!complete){yes=true;break;}
   Row a=s==retained?rt[bb]:tab[s][bb];
   x=(x&~(1<<(L+pos)))|(a.w<<(L+pos));pos+=a.d;s=mapped(a.z);
   for(auto const&g:c.goals)if(s==mapped(g.q)&&pos==g.h&&x==g.t){yes=true;break;}
   if(yes)break;
  }
  if(!yes)return false;
 }
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

 for(int q:states)for(int b=0;b<2;b++){
  for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:states){
   Row initial{w,d,z};if(w==tab[q][b].w&&d==tab[q][b].d&&z==tab[q][b].z)continue;
   checked++;bool allgood=true;int maxused=0;
   for(auto const&c:pre[q][b]){
    contexttests++;int t=(c.t&~(1<<L))|(w<<L),h=d,s=z;bool yes=false;
    for(int step=1;step<=maxnew;step++){
     for(auto const&g:c.goals)if(s==g.q&&h==g.h&&t==g.t){yes=true;break;}
     if(yes){maxused=max(maxused,step);break;}
     if(step==maxnew||s==254||h<-L||h>R)break;
     int bit=(t>>(h+L))&1;
     Row a=s==q&&bit==b?initial:tab[s][bit];
     t=(t&~(1<<(h+L)))|(a.w<<(h+L));h+=a.d;s=a.z;
    }
    if(!yes){allgood=false;break;}
   }
   if(allgood){cout<<q<<" "<<b<<" "<<w<<" "<<d<<" "<<z<<" "<<maxused<<endl;candidate++;}
  }
 }
 cerr<<"FINISHED checked "<<checked<<" candidates "<<candidate<<" contexttests "<<contexttests<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
