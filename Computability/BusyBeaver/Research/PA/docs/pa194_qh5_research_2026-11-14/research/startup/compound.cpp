#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};
struct E{int id,q,b;A a;};
struct Seed{int pc;string path;};
array<A,2> base[3000],rows[3000];vector<E> edits;vector<int> menus[6000],qs;
vector<Seed> seeds;set<vector<int>> visited;long long runs=0,ticks=0,hits=0;int bound=200000,depthmax=2;
void explore(int start,vector<int> ids){
 sort(ids.begin(),ids.end());vector<int> key=ids;key.insert(key.begin(),start);if(!visited.insert(key).second)return;
 for(int q:qs)rows[q]=base[q];for(int i:ids){auto e=edits[i];rows[e.q][e.b]=e.a;}
 int ray[3000]={};for(int v:qs){int q=v,d=0;set<int>s;while(q!=254&&!s.count(q)){s.insert(q);auto a=rows[q][0];if(d&&d!=a.d){d=0;break;}d=a.d;q=a.n;}if(d&&s.count(q))ray[v]=d;}
 set<int> ones,touched;int q=start,h=0;string status="limit";
 for(int st=0;st<=bound;st++){
  if(q==254){status="halt";break;}
  if(q==84&&ones.size()>=13){
   vector<int>x(ones.begin(),ones.end());
   for(auto seed:seeds){vector<int>pre{h-1};for(int j=0;j<(int)seed.path.size();j++)if(seed.path[j]=='1')pre.push_back(h+j);
    int m=pre.size();bool ok=x.size()>pre.size()&&equal(pre.begin(),pre.end(),x.begin())&&x[m]>=h+48;
    if(!ok)continue;vector<int> vals;int i=m+1,pos=x[m];while(ok&&i<(int)x.size()){if(x[i]!=pos+2){ok=false;break;}int len=1;pos=x[i++];while(i<(int)x.size()&&x[i]==pos+1){len++;pos=x[i++];}vals.push_back(len-1);}if(vals.size()<10)ok=false;
    if(ok){cout<<"HIT "<<start<<" "<<st<<" "<<seed.pc<<" "<<h<<" edits";for(int i:ids)cout<<" "<<i;cout<<" values";for(int v:vals)cout<<" "<<v;cout<<endl;hits++;status="hit";break;}
   }if(status=="hit")break;
  }
  if(st==bound||abs(h)>20000||ones.size()>20000)break;
  int b=ones.count(h);touched.insert(2*q+b);int d=ray[q];if(!b&&d&&(ones.empty()||(d==1&&h>*ones.rbegin())||(d==-1&&h<*ones.begin()))){status="ray";break;}
  A a=rows[q][b];if(a.w)ones.insert(h);else ones.erase(h);h+=a.d;q=a.n;ticks++;
 }
 runs++;if(runs%10000==0)cerr<<"runs "<<runs<<" ticks "<<ticks<<" seen "<<visited.size()<<" hits "<<hits<<endl;
 if((int)ids.size()>=depthmax||status=="hit")return;
 set<int> used;for(int i:ids)used.insert(edits[i].q*2+edits[i].b);
 for(int k:touched)if(!used.count(k))for(int i:menus[k]){auto z=ids;z.push_back(i);explore(start,z);}
}
int main(int argc,char**argv){ifstream f(argv[1]);int q,b,w,n;char d;set<int>Q;while(f>>q>>b>>w>>d>>n){base[q][b]={w,d=='R'?1:-1,n};Q.insert(q);}qs.assign(Q.begin(),Q.end());ifstream ef(argv[2]);E e;while(ef>>e.id>>e.q>>e.b>>e.a.w>>e.a.d>>e.a.n){menus[e.q*2+e.b].push_back(edits.size());edits.push_back(e);}ifstream sf(argv[3]);Seed s;int mask;while(sf>>s.pc>>s.path>>mask)seeds.push_back(s);depthmax=stoi(argv[4]);bound=stoi(argv[5]);int start=stoi(argv[6]);if(start<0){for(int q:qs)explore(q,{});}else explore(start,{});cerr<<"DONE runs "<<runs<<" ticks "<<ticks<<" hits "<<hits<<endl;}
