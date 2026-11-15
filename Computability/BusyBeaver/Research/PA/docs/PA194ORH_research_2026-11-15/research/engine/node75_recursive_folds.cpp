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

 long tried=0;
 for(int gone=0;gone<N;gone++)for(int keep=gone+1;keep<N;keep++){
  auto mapped=[&](int q){return q==gone?keep:q;};
  auto ok=[&](Act a0,Act a1)->bool {
   Act acts[2]={a0,a1};
   for(int old:{gone,keep})for(int b=0;b<2;b++)for(int p:ctx[old][b]){
    Act orig=tab[old][b];int end=mapped(orig.n),endpos=orig.d,exp=(p&~ctr)|(orig.w<<K);
    int tape=p,pos=0,st=keep;bool good=false;
    for(int k=1;k<=fuel;k++){
     if(st==N||abs(pos)>K)break;
     int bit=(tape>>(K+pos))&1;Act a=(st==keep?acts[bit]:tab[st][bit]);
     tape=(tape&~(1<<(K+pos)))|(a.w<<(K+pos));pos+=a.d;st=mapped(a.n);
     if(st==end&&pos==endpos&&tape==exp){good=true;break;}
    }
    if(!good)return false;
   }
   return true;
  };

  vector<Act>opts[2];
  for(int b=0;b<2;b++)for(int n=0;n<=N;n++)if(n!=gone)for(int w=0;w<2;w++)for(int d:{-1,1}){
   Act a={w,d,n};bool allgood=true;
   for(int old:{gone,keep}){
    for(int p:ctx[old][b]){
     Act orig=tab[old][b];int end=mapped(orig.n),endpos=orig.d,exp=(p&~ctr)|(orig.w<<K);
     int tape=(p&~ctr)|(a.w<<K),pos=a.d,st=a.n;bool good=false;
     for(int k=1;k<=fuel;k++){
      if(st==end&&pos==endpos&&tape==exp){good=true;break;}
      if(st==keep){good=true;break;}
      if(st==N||abs(pos)>K)break;
      Act at=tab[st][(tape>>(K+pos))&1];tape=(tape&~(1<<(K+pos)))|(at.w<<(K+pos));pos+=at.d;st=mapped(at.n);
     }
     if(!good){allgood=false;break;}
    }
    if(!allgood)break;
   }
   if(allgood)opts[b].push_back(a);
  }
  for(auto a0:opts[0])for(auto a1:opts[1]){
   tried++;
   if(ok(a0,a1))cout<<"MERGE "<<labs[gone]<<" "<<labs[keep]<<" with "<<a0.w<<" "<<a0.d<<" "<<(a0.n==N?254:labs[a0.n])<<" ; "<<a1.w<<" "<<a1.d<<" "<<(a1.n==N?254:labs[a1.n])<<"\n";
  }

 }
 cerr<<"tried "<<tried<<"\n";
}
