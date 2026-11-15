#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <vector>
#include <algorithm>
#include <chrono>
using namespace std;
struct Act{int w,d,n;bool operator<(const Act&a)const{return tie(w,d,n)<tie(a.w,a.d,a.n);}};
struct Conf{int tape,pos,st;};
int main(int argc,char**argv){
 string path=argv[1],prefix=argv[2];int K=argc>3?stoi(argv[3]):7,oldfuel=argc>4?stoi(argv[4]):3,newfuel=argc>5?stoi(argv[5]):15;
 auto begin=chrono::steady_clock::now();map<int,array<Act,2>>raw;ifstream in(path);string line;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,n;char d;if(!(s>>q>>b>>w>>d>>n))return 2;raw[q][b]={w,d=='R'?1:-1,n};}
 vector<int>labs;for(auto&[q,a]:raw)labs.push_back(q);map<int,int>ix;for(int i=0;i<(int)labs.size();i++)ix[labs[i]]=i;int N=labs.size();set<int>haltlabels;vector<array<Act,2>>tab(N);
 for(int i=0;i<N;i++)for(int b=0;b<2;b++){auto a=raw[labs[i]][b];if(!ix.count(a.n))haltlabels.insert(a.n);tab[i][b]={a.w,a.d,ix.count(a.n)?ix.at(a.n):N};}if(haltlabels.size()!=1)return 2;int halt=*haltlabels.begin(),start=ix.at(74);
 int W=2*K+1,P=1<<W,MASK=P-1,ctr=1<<K;vector<vector<unsigned char>>seen(N,vector<unsigned char>(P));queue<pair<int,int>>todo;todo.push({start,0});seen[start][0]=1;vector<array<vector<int>,2>>ctx(N);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();int b=(p>>K)&1;ctx[q][b].push_back(p);auto a=tab[q][b];if(a.n==N)continue;int r=(p&~ctr)|(a.w<<K),np=a.d==1?r>>1:(r<<1)&MASK,shift=a.d==1?W-1:0;for(int x=0;x<2;x++){int v=np|(x<<shift);if(!seen[a.n][v]){seen[a.n][v]=1;todo.push({a.n,v});}}}
 long total=0;for(auto&x:ctx)total+=x[0].size()+x[1].size();cerr<<"N "<<N<<" radius "<<K<<" contexts "<<total<<" oldfuel "<<oldfuel<<" newfuel "<<newfuel<<'\n';
 auto oldtrace=[&](int q,int p,vector<Conf>&out){out.clear();int tape=p,pos=0,st=q;for(int k=1;k<=oldfuel;k++){if(st==N||abs(pos)>K)break;auto a=tab[st][(tape>>(K+pos))&1];tape=(tape&~(1<<(K+pos)))|(a.w<<(K+pos));pos+=a.d;st=a.n;out.push_back({tape,pos,st});}};
 long tested=0;int matches=0;vector<Conf>targets;targets.reserve(oldfuel);
 for(int gone=0;gone<N;gone++)for(int keep=gone+1;keep<N;keep++){
  auto mapped=[&](int q){return q==gone?keep:q;};
  auto match=[&](int tape,int pos,int st){for(auto&c:targets)if(c.tape==tape&&c.pos==pos&&mapped(c.st)==st)return true;return false;};
  auto okay=[&](Act a0,Act a1){
   for(int old:{gone,keep})for(int b=0;b<2;b++)for(int p:ctx[old][b]){
    oldtrace(old,p,targets);int tape=p,pos=0,st=keep;bool good=false;
    for(int k=1;k<=newfuel;k++){
     if(st==N||abs(pos)>K)break;int bit=(tape>>(K+pos))&1;auto a=st==keep?(bit?a1:a0):tab[st][bit];tape=(tape&~(1<<(K+pos)))|(a.w<<(K+pos));pos+=a.d;st=mapped(a.n);
     if(match(tape,pos,st)){good=true;break;}
    }
    if(!good)return false;
   }
   return true;
  };
  array<vector<Act>,2>opts;
  for(int b=0;b<2;b++)for(int n=0;n<=N;n++)if(n!=gone)for(int w=0;w<2;w++)for(int d:{-1,1}){
   Act candidate={w,d,n};bool allgood=true;
   for(int old:{gone,keep}){
    for(int p:ctx[old][b]){
     oldtrace(old,p,targets);int tape=(p&~ctr)|(w<<K),pos=d,st=n;bool good=false;
     for(int k=1;k<=newfuel;k++){
      if(match(tape,pos,st)){good=true;break;}
      if(st==keep){good=true;break;}
      if(st==N||abs(pos)>K)break;
      auto a=tab[st][(tape>>(K+pos))&1];tape=(tape&~(1<<(K+pos)))|(a.w<<(K+pos));pos+=a.d;st=mapped(a.n);
     }
     if(!good){allgood=false;break;}
    }
    if(!allgood)break;
   }
   if(allgood)opts[b].push_back(candidate);
  }
  for(auto a0:opts[0])for(auto a1:opts[1]){
   tested++;if(!okay(a0,a1))continue;string stem=prefix+".candidate"+to_string(matches++);ofstream f(stem+".tm");
   for(int q=0;q<N;q++)if(q!=gone)for(int b=0;b<2;b++){auto a=q==keep?(b?a1:a0):tab[q][b];a.n=mapped(a.n);f<<labs[q]<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<(a.n==N?halt:labs[a.n])<<'\n';}
   cout<<"MERGE "<<labs[gone]<<' '<<labs[keep]<<" -> "<<a0.w<<' '<<a0.d<<' '<<(a0.n==N?halt:labs[a0.n])<<" ; "<<a1.w<<' '<<a1.d<<' '<<(a1.n==N?halt:labs[a1.n])<<" start "<<(start==gone?labs[keep]:labs[start])<<'\n'<<flush;
  }
 }
 cerr<<"joint_actions_tested "<<tested<<" merges "<<matches<<" elapsed "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<'\n';
}
