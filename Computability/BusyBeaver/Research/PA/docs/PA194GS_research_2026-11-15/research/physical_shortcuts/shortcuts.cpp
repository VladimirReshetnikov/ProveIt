#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <vector>
#include <algorithm>
using namespace std;
struct Act {int w,d,n;bool operator<(const Act&a)const{return tie(w,d,n)<tie(a.w,a.d,a.n);}bool operator==(const Act&a)const{return tie(w,d,n)==tie(a.w,a.d,a.n);}};
int main(int argc,char**argv){
 string path=argv[1],prefix=argv[2];int K=argc>3?stoi(argv[3]):6,F=argc>4?stoi(argv[4]):65;
 map<int,array<Act,2>>raw;ifstream in(path);int q,b,w,n;char d;
 while(in>>q>>b>>w>>d>>n)raw[q][b]={w,d=='R'?1:-1,n};
 vector<int>labs;for(auto&[q,a]:raw)labs.push_back(q);map<int,int>idx;for(int i=0;i<(int)labs.size();i++)idx[labs[i]]=i;int N=labs.size();idx[254]=N;vector<array<Act,2>>tab(N);
 for(int i=0;i<N;i++)for(int b=0;b<2;b++){auto a=raw[labs[i]][b];tab[i][b]={a.w,a.d,idx.at(a.n)};}
 int W=2*K+1,P=1<<W,MASK=P-1,ctr=1<<K;vector<vector<unsigned char>>seen(N,vector<unsigned char>(P));queue<pair<int,int>>todo;todo.push({idx.at(74),0});seen[idx.at(74)][0]=1;vector<array<vector<int>,2>>ctx(N);
 while(!todo.empty()){auto [q,p]=todo.front();todo.pop();int b=(p>>K)&1;ctx[q][b].push_back(p);auto a=tab[q][b];if(a.n==N)continue;int r=(p&~ctr)|(a.w<<K);int np=a.d==1?r>>1:(r<<1)&MASK;int shift=a.d==1?W-1:0;for(int x=0;x<2;x++){int v=np|(x<<shift);if(!seen[a.n][v]){seen[a.n][v]=1;todo.push({a.n,v});}}}
 long total=0;for(auto &x:ctx)total+=x[0].size()+x[1].size();cerr<<"N "<<N<<" K "<<K<<" contexts "<<total<<endl;
 vector<array<vector<Act>,2>>opts(N);ofstream outf(prefix+".options.tsv");outf<<"state\tread\twrite\tmove\tnext\tcontexts\n";
 for(int q=0;q<N;q++)for(int b=0;b<2;b++){
  set<Act>common;bool first=true;
  for(int p:ctx[q][b]){
   set<Act>local;int tape=p,pos=0,st=q;
   for(int k=1;k<=F;k++){
    if(st==N||abs(pos)>K)break;
    int bit=(tape>>(K+pos))&1;auto a=tab[st][bit];tape=(tape&~(1<<(K+pos)))|(a.w<<(K+pos));pos+=a.d;st=a.n;
    if(abs(pos)==1&&(tape&~ctr)==(p&~ctr))local.insert({(tape>>K)&1,pos,st});
   }
   if(first){common=local;first=false;}else{set<Act>next;set_intersection(common.begin(),common.end(),local.begin(),local.end(),inserter(next,next.end()));common=next;}
   if(common.size()==1&&*common.begin()==tab[q][b])break;
  }
  if(first)for(int nn=0;nn<=N;nn++)common.insert({0,1,nn});
  opts[q][b]=vector<Act>(common.begin(),common.end());
  stable_sort(opts[q][b].begin(),opts[q][b].end(),[&](Act a,Act c){return (a==tab[q][b])>(c==tab[q][b]);});
  for(auto a:opts[q][b]){outf<<labs[q]<<'\t'<<b<<'\t'<<a.w<<'\t'<<(a.d==1?'R':'L')<<'\t'<<(a.n==N?254:labs[a.n])<<'\t'<<ctx[q][b].size()<<'\n';if(!(a==tab[q][b]))cout<<"OPTION "<<labs[q]<<' '<<b<<" -> "<<a.w<<' '<<a.d<<' '<<(a.n==N?254:labs[a.n])<<'\n';}
 }
 int count=0;
 auto omit=[&](set<int>S){if(S.count(idx.at(74)))return;for(int q=0;q<N;q++)if(!S.count(q))for(int b=0;b<2;b++)if(none_of(opts[q][b].begin(),opts[q][b].end(),[&](Act a){return !S.count(a.n);}))return;
  ofstream f(prefix+".candidate"+to_string(count++)+".tm");for(int q=0;q<N;q++)if(!S.count(q))for(int b=0;b<2;b++){auto a=*find_if(opts[q][b].begin(),opts[q][b].end(),[&](Act a){return !S.count(a.n);});f<<labs[q]<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<(a.n==N?254:labs[a.n])<<'\n';}cout<<"REMOVABLE";for(int q:S)cout<<' '<<labs[q];cout<<endl;
 };
 for(int q=0;q<N;q++)omit({q});for(int q=0;q<N;q++)for(int r=q+1;r<N;r++)omit({q,r});

 for(int gone=0;gone<N;gone++)for(int keep=gone+1;keep<N;keep++){
  if(gone==idx.at(74))continue;
  auto remap=[&](Act a){if(a.n==gone)a.n=keep;return a;};
  array<set<Act>,2>shared;bool valid=true;
  for(int bit=0;bit<2;bit++){
   set<Act>aa,bb;for(auto a:opts[gone][bit])aa.insert(remap(a));for(auto a:opts[keep][bit])bb.insert(remap(a));
   set_intersection(aa.begin(),aa.end(),bb.begin(),bb.end(),inserter(shared[bit],shared[bit].end()));
   if(shared[bit].empty())valid=false;
  }
  if(!valid)continue;
  ofstream f(prefix+".candidate"+to_string(count++)+".tm");
  for(int q=0;q<N;q++)if(q!=gone)for(int bit=0;bit<2;bit++){
   Act a=q==keep?*shared[bit].begin():remap(tab[q][bit]);
   f<<labs[q]<<' '<<bit<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<(a.n==N?254:labs[a.n])<<'\n';
  }
  cout<<"MERGABLE "<<labs[gone]<<' '<<labs[keep]<<endl;
 }
 cerr<<"CANDIDATES "<<count<<endl;
}
