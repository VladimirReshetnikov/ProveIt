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
 auto valid=[&](int q,int b,Act a,Cand&cand)->bool{
  auto target=tab[q][b];bitset<256>used;int maxlen=1;
  if(ctx[q][b].empty()) {cand={a,used,0};return true;}
  for(int p:ctx[q][b]){int exp=(p&~ctr)|(target.w<<K);int tape=(p&~ctr)|(a.w<<K),pos=a.d,state=a.n;bool good=false;
   for(int k=1;k<=fuel;k++){
    if(state==target.n&&pos==target.d&&tape==exp){good=true;maxlen=max(maxlen,k);break;}
    if(state==N||abs(pos)>K)break;
    used[state]=true;auto s=tab[state][(tape>>(pos+K))&1];tape=(tape&~(1<<(pos+K)))|(s.w<<(pos+K));pos+=s.d;state=s.n;
   }
   if(!good)return false;
  }
  cand={a,used,maxlen};return true;
 };
 vector<array<vector<Cand>,2>>cs(N);
 for(int q=0;q<N;q++){for(int b=0;b<2;b++){for(int n=0;n<=N;n++)for(int w=0;w<2;w++)for(int d:{-1,1}){Cand c;if(valid(q,b,{w,d,n},c))cs[q][b].push_back(c);}}
  cerr<<labs[q]<<":"<<cs[q][0].size()<<","<<cs[q][1].size()<<" ";if(q%10==9)cerr<<"\n";
 }
 cerr<<"\n";
 if(argc>4){ofstream ff(argv[4]);for(int q=0;q<N;q++)for(int b=0;b<2;b++)for(auto c:cs[q][b])if(!c.visited[q]&&!(c.act==tab[q][b]))ff<<labs[q]<<" "<<b<<" "<<c.act.w<<" "<<(c.act.d==1?'R':'L')<<" "<<(c.act.n==N?254:labs[c.act.n])<<" "<<c.maxlen<<"\n";}
 for(int q=0;q<N;q++)for(int r=q+1;r<N;r++){
  
  vector<pair<Cand,Cand>>both[2];
  for(int b=0;b<2;b++)for(auto& a:cs[q][b])for(auto& c:cs[r][b]){Act aa=a.act,cc=c.act; if(aa.n==q)aa.n=r;if(cc.n==q)cc.n=r;if(aa==cc&&!a.visited[q]&&!a.visited[r]&&!c.visited[q]&&!c.visited[r])both[b].push_back({a,c});}
  if(both[0].empty()||both[1].empty())continue;
  cout<<"MERGE "<<labs[q]<<" -> "<<labs[r]<<" choices "<<both[0].size()<<" "<<both[1].size()<<"\n";
  for(int b=0;b<2;b++)for(auto&[a,c]:both[b])cout<<b<<" "<<a.act.w<<" "<<(a.act.d==1?'R':'L')<<" "<<(a.act.n==N?254:labs[a.act.n])<<" length "<<a.maxlen<<","<<c.maxlen<<"\n";
 }
}
