#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <algorithm>
#include <array>
#include <cstring>
#include <cmath>
using namespace std;
struct Act{int w,d,t;}; struct Mut{int q,b;Act a;};
Act base[3000][2],tab[3000][2];vector<Mut> ms;vector<int> controls;vector<pair<int,string>> paths;
int tape[40001]; const int O=20000;int maxsteps=200000,rangebound=1500;
// Status:0 fuel bound,1 seed,2 halt,3 outward ray,4 range bound,5 missing row.
struct Run{int status,n,site,head,gap;vector<int> values;set<pair<int,int>> keys;};
bool frame(int h,int mn,int mx,Run&r){
 if(h<=1||h>=39900||!tape[h-1])return false;
 for(int k=mn;k<h-1;k++)if(tape[k])return false;
 for(auto&[site,p]:paths){
  bool ok=true;for(int j=0;j<(int)p.size();j++)if(tape[h+j]!=(p[j]-'0')){ok=false;break;}if(!ok)continue;
  int j=h+p.size();while(j<=mx&&!tape[j])j++;
  if(j-h<48||j>mx||tape[j+1])continue;
  int gap=j-h;vector<int>vals;j++;
  while(j<=mx&&tape[j]==0&&tape[j+1]){int x=j+1;while(x<=mx&&tape[x])x++;vals.push_back(x-j-2);j=x;}
  if(vals.size()<10)continue;
  for(int k=j;k<=mx;k++)if(tape[k]){ok=false;break;}if(!ok)continue;
  r.site=site;r.head=h-O;r.gap=gap;r.values=vals;return true;
 }
 return false;
}
Run sim(int start,bool track=false){
 memset(tape,0,sizeof tape);int q=start,h=O,mn=O,mx=O;Run r;r.status=0;
 for(int n=0;n<maxsteps;n++){
  r.n=n;
  if(q==84&&frame(h,mn,mx,r)){r.status=1;return r;}
  if(q==254){r.status=2;return r;}
  int b=tape[h];if(track)r.keys.insert({q,b});
  auto a=tab[q][b];
  if(a.t<0){r.status=5;return r;}
  if(a.t==q&&b==0&&((h>mx&&a.d==1)||(h<mn&&a.d==-1))){r.status=3;return r;}
  tape[h]=a.w;if(a.w){mn=min(mn,h);mx=max(mx,h);}h+=a.d;q=a.t;r.n=n+1;
  if(abs(h-O)>rangebound){r.status=4;return r;}
 }
 return r;
}
void hit(const vector<int>&ii,int st,Run&r){cout<<"HIT "<<st<<" edits";for(int i:ii)cout<<" "<<i;cout<<" steps "<<r.n<<" site "<<r.site<<" head "<<r.head<<" gap "<<r.gap<<" vals";for(int v:r.values)cout<<" "<<v;cout<<endl;}
int main(int argc,char**argv){
 if(argc<2){cerr<<"Usage: bootstrap_pairs INPUT_DIRECTORY [triples]\n";return 2;}
 string dir=argv[1];for(int q=0;q<3000;q++)for(int b=0;b<2;b++)base[q][b]={0,1,-1};
 ifstream in(dir+"/runtime193.native.tm");int q,b,w,t;char d;while(in>>q>>b>>w>>d>>t){base[q][b]={w,d=='R'?1:-1,t};if(b==0)controls.push_back(q);}
 ifstream mfile(dir+"/neutral193.tsv");int di;while(mfile>>q>>b>>w>>di>>t)ms.push_back({q,b,{w,di,t}});
 ifstream pfile(dir+"/seedpaths.txt");int site;string p;while(pfile>>site>>p)paths.push_back({site,p});
 if(controls.size()!=193||ms.size()!=346||paths.size()!=20){cerr<<"Unexpected input counts\n";return 2;}
 for(auto m:ms)if(m.q<0||m.q>=3000||m.b<0||m.b>1||base[m.q][m.b].t<0||m.a.w<0||m.a.w>1||(m.a.d!=1&&m.a.d!=-1)||m.a.t<0||m.a.t>=3000||(m.a.t!=254&&base[m.a.t][0].t<0)){cerr<<"Invalid proposal\n";return 2;}
 memcpy(tab,base,sizeof tab);auto orig=sim(74,true);cout<<"base "<<orig.status<<" steps "<<orig.n<<" keys "<<orig.keys.size()<<endl;
 long long trials=0,steps=0;array<long long,6>counts{};set<pair<int,int>>done;vector<pair<int,int>>allpairs;
 for(int i=0;i<(int)ms.size();i++){
  auto a=ms[i];if(!orig.keys.count({a.q,a.b}))continue;
  tab[a.q][a.b]=a.a;auto first=sim(74,true);tab[a.q][a.b]=base[a.q][a.b];if(first.status==1)hit({i},74,first);
  for(int j=0;j<(int)ms.size();j++){
   auto z=ms[j];if(i==j||(a.q==z.q&&a.b==z.b)||!first.keys.count({z.q,z.b}))continue;
   pair<int,int>pairr={min(i,j),max(i,j)};if(done.count(pairr))continue;done.insert(pairr);allpairs.push_back(pairr);
   tab[a.q][a.b]=a.a;tab[z.q][z.b]=z.a;
   auto rr=sim(74);trials++;steps+=rr.n;counts[rr.status]++;if(rr.status==1)hit({i,j},74,rr);
   tab[a.q][a.b]=base[a.q][a.b];tab[z.q][z.b]=base[z.q][z.b];
  }
 }
 cout<<"PAIRS trials "<<trials<<" steps "<<steps<<" status";for(auto v:counts)cout<<" "<<v;cout<<endl;
 if(argc>2){
  set<array<int,3>>done3;trials=0;steps=0;counts={};
  for(auto ij:allpairs){int i=ij.first,j=ij.second;auto a=ms[i],z=ms[j];tab[a.q][a.b]=a.a;tab[z.q][z.b]=z.a;auto rr=sim(74,true);
   for(int k=0;k<(int)ms.size();k++){
    auto c=ms[k];if(k==i||k==j||(c.q==a.q&&c.b==a.b)||(c.q==z.q&&c.b==z.b)||!rr.keys.count({c.q,c.b}))continue;
    array<int,3>triple{i,j,k};sort(triple.begin(),triple.end());if(done3.count(triple))continue;done3.insert(triple);
    tab[c.q][c.b]=c.a;auto ss=sim(74);trials++;steps+=ss.n;counts[ss.status]++;if(ss.status==1)hit({i,j,k},74,ss);tab[c.q][c.b]=base[c.q][c.b];
   }
   tab[a.q][a.b]=base[a.q][a.b];tab[z.q][z.b]=base[z.q][z.b];
  }
  cout<<"TRIPLES trials "<<trials<<" steps "<<steps<<" status";for(auto v:counts)cout<<" "<<v;cout<<endl;
 }
}
