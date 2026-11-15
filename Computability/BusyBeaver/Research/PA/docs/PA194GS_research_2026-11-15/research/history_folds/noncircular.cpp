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
#include <chrono>
using namespace std;
struct Act{int w,d,n;bool operator<(const Act&a)const{return tie(w,d,n)<tie(a.w,a.d,a.n);}bool operator==(const Act&a)const{return tie(w,d,n)==tie(a.w,a.d,a.n);}};
struct Option{Act action;bitset<256>visited;int maxsteps;};
int main(int argc,char**argv){
 string path=argv[1],prefix=argv[2];int K=argc>3?stoi(argv[3]):7,F=argc>4?stoi(argv[4]):15;
 auto began=chrono::steady_clock::now();map<int,array<Act,2>>raw;ifstream in(path);string line;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,n;char d;if(!(s>>q>>b>>w>>d>>n)){cerr<<"bad input\n";return 2;}raw[q][b]={w,d=='R'?1:-1,n};}
 vector<int>labs;for(auto&[q,a]:raw)labs.push_back(q);map<int,int>idx;for(int i=0;i<(int)labs.size();i++)idx[labs[i]]=i;int N=labs.size();if(N>=256)return 2;vector<array<Act,2>>tab(N);set<int>halts;
 for(int i=0;i<N;i++)for(int b=0;b<2;b++){auto a=raw[labs[i]][b];if(!idx.count(a.n))halts.insert(a.n);tab[i][b]={a.w,a.d,idx.count(a.n)?idx.at(a.n):N};}if(halts.size()!=1){cerr<<"nonunique halt\n";return 2;}int halt=*halts.begin();int start=idx.count(74)?idx.at(74):idx.at(0);
 int W=2*K+1,P=1<<W,MASK=P-1,ctr=1<<K;vector<vector<unsigned char>>seen(N,vector<unsigned char>(P));queue<pair<int,int>>todo;todo.push({start,0});seen[start][0]=1;vector<array<vector<int>,2>>ctx(N);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();int b=(p>>K)&1;ctx[q][b].push_back(p);auto a=tab[q][b];if(a.n==N)continue;int r=(p&~ctr)|(a.w<<K),np=a.d==1?r>>1:(r<<1)&MASK,shift=a.d==1?W-1:0;for(int x=0;x<2;x++){int v=np|(x<<shift);if(!seen[a.n][v]){seen[a.n][v]=1;todo.push({a.n,v});}}}
 long total=0;for(auto&x:ctx)total+=x[0].size()+x[1].size();cerr<<"N "<<N<<" radius "<<K<<" contexts "<<total<<"\n";
 vector<array<vector<Option>,2>>options(N);long tried=0,passed=0;
 for(int q=0;q<N;q++)for(int b=0;b<2;b++){
  Act target=tab[q][b];
  for(int n=0;n<=N;n++)for(int w=0;w<2;w++)for(int d:{-1,1}){
   Act candidate={w,d,n};Option op={candidate,{},0};bool allgood=true;tried++;
   for(int p:ctx[q][b]){
    int tape=(p&~ctr)|(w<<K),pos=d,st=n,expected=(p&~ctr)|(target.w<<K);bool good=false;bitset<256>visited;
    for(int k=1;k<=F;k++){
     if(st==target.n&&pos==target.d&&tape==expected){good=true;op.maxsteps=max(op.maxsteps,k);break;}
     if(st==q||st==N||abs(pos)>K)break;
     visited.set(st);auto a=tab[st][(tape>>(K+pos))&1];tape=(tape&~(1<<(K+pos)))|(a.w<<(K+pos));pos+=a.d;st=a.n;
    }
    if(!good){allgood=false;break;}op.visited|=visited;
   }
   if(allgood){options[q][b].push_back(op);passed++;}
  }
 }
 ofstream optfile(prefix+".options.tsv");optfile<<"state\tread\twrite\tmove\tnext\tmaxsteps\tinterior_controls\n";
 for(int q=0;q<N;q++)for(int b=0;b<2;b++)for(auto&o:options[q][b]){optfile<<labs[q]<<'\t'<<b<<'\t'<<o.action.w<<'\t'<<(o.action.d==1?'R':'L')<<'\t'<<(o.action.n==N?halt:labs[o.action.n])<<'\t'<<o.maxsteps<<'\t';for(int i=0;i<N;i++)if(o.visited[i])optfile<<labs[i]<<',';optfile<<'\n';}
 int matches=0;
 for(int gone=0;gone<N;gone++)for(int keep=gone+1;keep<N;keep++){
  auto mapact=[&](Act a){if(a.n==gone)a.n=keep;return a;};array<vector<Act>,2>shared;
  for(int b=0;b<2;b++)for(auto&a:options[gone][b])if(!a.visited[keep])for(auto&c:options[keep][b])if(!c.visited[gone]&&mapact(a.action)==mapact(c.action))shared[b].push_back(mapact(a.action));
  if(shared[0].empty()||shared[1].empty())continue;
  for(auto a0:shared[0])for(auto a1:shared[1]){
   // Full independent check under the actual quotient, not just option intersection.
   bool valid=true;int maxlen=0;
   for(int old:{gone,keep})for(int b=0;b<2;b++)for(int p:ctx[old][b]){
    auto orig=mapact(tab[old][b]);int exp=(p&~ctr)|(orig.w<<K);int st=keep,pos=0,tape=p;bool good=false;
    for(int k=1;k<=F;k++){
     if(st==N||abs(pos)>K)break;int bit=(tape>>(K+pos))&1;Act a=st==keep?(bit?a1:a0):mapact(tab[st][bit]);tape=(tape&~(1<<(K+pos)))|(a.w<<(K+pos));pos+=a.d;st=a.n;
     if(st==orig.n&&pos==orig.d&&tape==exp){good=true;maxlen=max(maxlen,k);break;}
    }
    if(!good)valid=false;
   }
   if(!valid){cerr<<"internal mismatch\n";return 3;}
   string stem=prefix+".candidate"+to_string(matches++);ofstream f(stem+".tm");
   for(int q=0;q<N;q++)if(q!=gone)for(int b=0;b<2;b++){Act a=q==keep?(b?a1:a0):mapact(tab[q][b]);f<<labs[q]<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<(a.n==N?halt:labs[a.n])<<'\n';}
   cout<<"MERGE "<<labs[gone]<<' '<<labs[keep]<<" -> "<<a0.w<<' '<<a0.d<<' '<<(a0.n==N?halt:labs[a0.n])<<" ; "<<a1.w<<' '<<a1.d<<' '<<(a1.n==N?halt:labs[a1.n])<<" maxsteps "<<maxlen<<" start "<<(start==gone?labs[keep]:labs[start])<<'\n';
  }
 }
 cerr<<"row_candidates "<<tried<<" valid_options "<<passed<<" merges "<<matches<<" elapsed "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
}
