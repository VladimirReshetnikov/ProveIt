// Sound finite-window reachability followed by bounded local macro contraction.
// Read symbols, writes and moves are preserved exactly by a successful witness.
// This is a restricted search, not a lower bound on arbitrary machines.
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
struct Act{int w,m,n;};struct Config{int x,p,q;};struct Case{int x;vector<Config> goals;};
int main(int argc,char**argv){
 if(argc<4){cerr<<"table radius max_old_steps [new_steps]\n";return 1;}
 int r=stoi(argv[2]),oldfuel=stoi(argv[3]),newfuel=argc>4?stoi(argv[4]):16;
 if(r<1||r>8)return 2;
 map<pair<int,int>,Act> raw;set<int> labels;string line;ifstream f(argv[1]);
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,n;char m;s>>q>>b>>w>>m>>n;raw[{q,b}]={w,m=='R'?1:-1,n};labels.insert(q);}
 vector<int> labs(labels.begin(),labels.end());int N=labs.size();map<int,int> ix;for(int i=0;i<N;i++)ix[labs[i]]=i;
 vector<array<Act,2>> rows(N);for(int i=0;i<N;i++)for(int b=0;b<2;b++){Act a=raw.at({labs[i],b});a.n=ix.count(a.n)?ix[a.n]:N;rows[i][b]=a;}
 int start=ix.at(74),width=2*r+1,W=1<<width,center=1<<r;
 vector<vector<unsigned char>> seen(N,vector<unsigned char>(W));vector<vector<int>>ctx(N);queue<pair<int,int>>todo;seen[start][0]=1;todo.push({start,0});
 while(!todo.empty()){
  auto[q,x]=todo.front();todo.pop();ctx[q].push_back(x);auto a=rows[q][(x>>r)&1];if(a.n==N)continue;
  x=(x&~center)|(a.w<<r);int y=a.m==1?x>>1:(x<<1)&(W-1),bit=a.m==1?1<<(width-1):1;
  for(int z:{y,y|bit})if(!seen[a.n][z]){seen[a.n][z]=1;todo.push({a.n,z});}
 }
 vector<array<vector<Case>,2>>tests(N);long total=0;
 for(int q=0;q<N;q++)for(int x:ctx[q]){total++;Case c{x,{}};int y=x,p=0,s=q;
  for(int k=0;k<oldfuel;k++){auto a=rows[s][(y>>(r+p))&1];y=(y&~(1<<(r+p)))|(a.w<<(r+p));p+=a.m;s=a.n;c.goals.push_back({y,p,s});if(abs(p)>r||s==N)break;}
  tests[q][(x>>r)&1].push_back(c);
 }
 cout<<"contexts "<<total<<" radius "<<r<<" oldfuel "<<oldfuel<<" newfuel "<<newfuel<<endl;
 long pairs=0,proposals=0,hits=0;
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++){
  pairs++;array<vector<Act>,2>choices;
  for(int bit=0;bit<2;bit++){
   for(int w=0;w<2;w++)for(int m:{-1,1})for(int dest=0;dest<=N;dest++){
    if(dest==a)continue;Act act{w,m,dest};bool good=true;
    for(int q:{a,b}){if(!good)break;for(auto&c:tests[q][bit]){
     int x=c.x,p=0,s=b;bool found=false;
     for(int k=0;k<newfuel;k++){
      Act ac=k==0?act:rows[s][(x>>(r+p))&1];x=(x&~(1<<(r+p)))|(ac.w<<(r+p));p+=ac.m;s=ac.n==a?b:ac.n;
      for(auto&g:c.goals)if(g.x==x&&g.p==p&&(g.q==a?b:g.q)==s){found=true;break;}
      if(found||abs(p)>r||s==N||s==b)break;
     }
     if(!found){good=false;break;}
    }}
    if(good){choices[bit].push_back(act);proposals++;}
   }
   if(choices[bit].empty())break;
  }
  if(!choices[0].empty()&&!choices[1].empty()){
   hits++;cout<<"HIT "<<labs[a]<<" -> "<<labs[b]<<" ";
   for(int bit=0;bit<2;bit++){cout<<"read"<<bit<<":";for(auto ac:choices[bit])cout<<ac.w<<(ac.m==1?'R':'L')<<(ac.n==N?254:labs[ac.n])<<",";}cout<<endl;
  }
 }
 cout<<"COMPLETE pairs "<<pairs<<" proposals "<<proposals<<" hits "<<hits<<endl;
}
