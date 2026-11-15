#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <vector>
#include <algorithm>
using namespace std;
struct Act { int w,d,n; bool operator==(const Act& a)const{return w==a.w&&d==a.d&&n==a.n;} bool operator<(const Act&a)const{return tie(w,d,n)<tie(a.w,a.d,a.n);} };
struct Cand {Act act; bitset<256> visited; int maxlen;};
int main(int argc,char**argv){
 int K=argc>2?stoi(argv[2]):5, fuel=argc>3?stoi(argv[3]):32; string path=argv[1];
 map<int,array<Act,2>> raw; ifstream in(path);int q,b,w,n;char d;
 while(in>>q>>b>>w>>d>>n)raw[q][b]={w,d=='R'?1:-1,n};
 vector<int>labs;for(auto&[q,a]:raw)labs.push_back(q);map<int,int>idx;for(int i=0;i<(int)labs.size();i++)idx[labs[i]]=i;int N=labs.size();idx[254]=N;
 vector<array<Act,2>>tab(N);for(int i=0;i<N;i++)for(int b=0;b<2;b++){auto a=raw[labs[i]][b];tab[i][b]={a.w,a.d,idx.at(a.n)};}
 int W=2*K+1,P=1<<W,MASK=P-1,ctr=1<<K;
 vector<vector<unsigned char>>seen(N,vector<unsigned char>(P));queue<pair<int,int>>todo;todo.push({idx.at(74),0});seen[idx.at(74)][0]=1;
 vector<array<vector<int>,2>>ctx(N);
 while(!todo.empty()) {auto [q,p]=todo.front();todo.pop();int b=(p>>K)&1;ctx[q][b].push_back(p);auto a=tab[q][b]; if(a.n==N)continue;int r=(p&~ctr)|(a.w<<K);int np=a.d==1?r>>1:(r<<1)&MASK;int shift=a.d==1?W-1:0;for(int x=0;x<2;x++){int v=np|(x<<shift);if(!seen[a.n][v]){seen[a.n][v]=1;todo.push({a.n,v});}}}
 cerr<<"N "<<N<<" K "<<K<<" contexts "; long total=0;for(int q=0;q<N;q++){auto z=ctx[q][0].size()+ctx[q][1].size();total+=z;if(!z)cerr<<" UNUSED "<<labs[q];}cerr<<total<<"\n";

 for(int gone=0;gone<N;gone++) {
  if(labs[gone]==74||tab[gone][0].n==gone||tab[gone][1].n==gone)continue;
  vector<pair<int,int>>edges;bitset<512>forbidden;
  for(int q=0;q<N;q++)for(int b=0;b<2;b++)if(tab[q][b].n==gone){edges.push_back({q,b});forbidden[2*q+b]=true;}
  vector<vector<pair<Act,int>>>choices;bool success=true;
  for(auto[q,b]:edges){
   vector<pair<Act,int>>options;
   for(int n=0;n<=N;n++)for(int w=0;w<2;w++)for(int d:{-1,1}){
    Act a={w,d,n}; if(n==gone)continue;bool goodall=true;int maxlen=0;
    for(int p:ctx[q][b]){
     Act fst=tab[q][b];int mid=(p&~ctr)|(fst.w<<K);Act snd=tab[gone][(mid>>(K+fst.d))&1];
     int exp=(mid&~(1<<(K+fst.d)))|(snd.w<<(K+fst.d)),endpos=fst.d+snd.d,endstate=snd.n;
     struct Conf{int st,pos,tape;};vector<Conf>goals;goals.push_back({endstate,endpos,exp});
     int ost=endstate,opos=endpos,otape=exp;
     for(int j=2;j<16;j++){
      if(ost==N||abs(opos)>K)break;Act ot=tab[ost][(otape>>(K+opos))&1];
      otape=(otape&~(1<<(opos+K)))|(ot.w<<(opos+K));opos+=ot.d;ost=ot.n;goals.push_back({ost,opos,otape});
     }
     int tape=(p&~ctr)|(a.w<<K),pos=a.d,state=a.n;bool good=false;
     for(int k=1;k<=fuel;k++){
      for(auto g:goals)if(state==g.st&&pos==g.pos&&tape==g.tape){good=true;maxlen=max(maxlen,k);break;}
      if(good)break;
      if(state==N||state==gone||abs(pos)>K)break;
      int bit=(tape>>(pos+K))&1;if(forbidden[2*state+bit])break;
      Act st=tab[state][bit];tape=(tape&~(1<<(pos+K)))|(st.w<<(pos+K));pos+=st.d;state=st.n;
     }
     if(!good){goodall=false;break;}
    }
    if(goodall)options.push_back({a,maxlen});
   }
   if(options.empty()){success=false;break;}choices.push_back(options);
  }
  if(!success)continue;
  cout<<"ELIMINATE "<<labs[gone]<<" incoming "<<edges.size()<<"\n";
  for(int i=0;i<(int)edges.size();i++)for(auto[a,len]:choices[i])cout<<labs[edges[i].first]<<" "<<edges[i].second<<" "<<a.w<<" "<<(a.d==1?'R':'L')<<" "<<(a.n==N?254:labs[a.n])<<" length "<<len<<"\n";
 }
}
