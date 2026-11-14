// Exhaust physical-register permutations; blank starts canonicalized at first 1 write.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};struct Seed{int pc;string path;int unused;};
int main(int argc,char**argv){
 if(argc<4){cerr<<"table seed_templates bound [first_permutation last_permutation]\n";return 2;}
 int bound=stoi(argv[3]),lo=argc>4?stoi(argv[4]):0,hi=argc>5?stoi(argv[5]):INT_MAX;
 array<A,2> base[4000],row[4000];bool ex[4000]={};vector<int>states;ifstream f(argv[1]);int q,b,w,n;char dr;
 while(f>>q>>b>>w>>dr>>n){if(!ex[q])states.push_back(q);ex[q]=true;base[q][b]={w,dr=='R'?1:-1,n};}
 vector<Seed>seeds;unordered_map<uint64_t,vector<Seed>>byhash;ifstream sf(argv[2]);Seed seed;
 while(sf>>seed.pc>>seed.path>>seed.unused){seeds.push_back(seed);uint64_t m=0;for(int j=0;j<(int)seed.path.size();j++)if(seed.path[j]=='1')m|=1ull<<j;byhash[m].push_back(seed);}
 const array<int,9>sk={51,36,25,48,32,33,22,55,60},logical={6,2,0,4,3,7,8,5,1};
 map<int,int>skindex;for(int i=0;i<9;i++)skindex[sk[i]]=i;
 vector<pair<int,int>> routers;for(int q:states){row[q]=base[q];A a=base[q][1];if(a.w==0&&a.d==1&&skindex.count(a.n))routers.push_back({q,skindex[a.n]});}
 cerr<<"ROUTERS ";for(auto[q,i]:routers)cerr<<q<<":"<<i<<" ";cerr<<"\n";
 vector<int>starts;starts.push_back(74);for(int q:states)if(base[q][0].w&&q!=74)starts.push_back(q);
 int raydir[4000]={};for(int q:states){int r=q,d=0;set<int>seen;while(r>=0&&r<4000&&ex[r]&&!seen.count(r)){seen.insert(r);A a=base[r][0];if(d&&a.d!=d){d=0;break;}d=a.d;r=a.n;}if(d&&seen.count(r))raydir[q]=d;}
 array<int,9>perm={0,1,2,3,4,5,6,7,8};long long permutations=0,simulations=0,ticks=0,halts=0,rays=0,limits=0,unsafe=0,frames=0;int index=-1;auto starttime=chrono::steady_clock::now();
 do{index++;if(index<lo)continue;if(index>=hi)break;permutations++;
  for(auto[q,i]:routers)row[q][1].n=sk[perm[i]];
  for(int start:starts){simulations++;int q=start,h=0;set<int>ones;bool ended=false;
   for(int st=0;st<=bound;st++){
    if(q==254){halts++;ended=true;break;}
    if(q==84&&ones.size()>=13&&*ones.begin()==h-1){uint64_t mask=0;for(auto it=next(ones.begin());it!=ones.end()&&*it<h+48;++it)mask|=1ull<<(*it-h);auto sit=byhash.find(mask);
     if(sit!=byhash.end())for(auto seed:sit->second){vector<int>x(ones.begin(),ones.end()),prefix{h-1};for(int j=0;j<(int)seed.path.size();j++)if(seed.path[j]=='1')prefix.push_back(h+j);size_t m=prefix.size();bool ok=x.size()>m&&equal(prefix.begin(),prefix.end(),x.begin())&&x[m]>=h+48;if(!ok)continue;int gap=x[m]-h-48;vector<int>values;size_t i=m+1;int pos=x[m];
      while(ok&&i<x.size()){if(x[i]!=pos+2){ok=false;break;}int len=1;pos=x[i++];while(i<x.size()&&x[i]==pos+1){len++;pos=x[i++];}values.push_back(len-1);}if(values.size()<10)ok=false;if(!ok)continue;frames++;
      if(values[perm[0]]||values[perm[2]]||values[perm[7]]){unsafe++;continue;}
      cout<<"{\"permutation_index\":"<<index<<",\"permutation\":[";for(int j=0;j<9;j++){if(j)cout<<',';cout<<perm[j];}cout<<"],\"logical_to_physical\":[";for(int j=0;j<9;j++){if(j)cout<<',';cout<<perm[logical[j]];}cout<<"],\"start\":"<<start<<",\"steps\":"<<st<<",\"head\":"<<h<<",\"pc\":"<<seed.pc<<",\"gap\":"<<gap<<",\"values\":[";for(int j=0;j<(int)values.size();j++){if(j)cout<<',';cout<<values[j];}cout<<"],\"ones\":[";for(int j=0;j<(int)x.size();j++){if(j)cout<<',';cout<<x[j];}cout<<"]}"<<endl;
      cerr<<"SUCCESS permutations "<<permutations<<" simulations "<<simulations<<" ticks "<<ticks<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-starttime).count()<<"\n";return 0;
     }
    }
    if(st==bound||abs(h)>20000||ones.size()>20000){limits++;ended=true;break;}
    bool bit=ones.count(h);int rd=raydir[q];if(!bit&&rd&&((rd==1&&(ones.empty()||*ones.rbegin()<h))||(rd==-1&&(ones.empty()||*ones.begin()>h)))){rays++;ended=true;break;}
    A a=row[q][bit];if(a.w)ones.insert(h);else ones.erase(h);h+=a.d;q=a.n;ticks++;
   }
  }
  if(permutations%10000==0)cerr<<"PROGRESS "<<index<<" permutations "<<permutations<<" simulations "<<simulations<<" ticks "<<ticks<<" unsafe "<<unsafe<<" limits "<<limits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-starttime).count()<<"\n";
 }while(next_permutation(perm.begin(),perm.end()));
 cerr<<"DONE permutations "<<permutations<<" simulations "<<simulations<<" ticks "<<ticks<<" halts "<<halts<<" rays "<<rays<<" limits "<<limits<<" frames "<<frames<<" unsafe "<<unsafe<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-starttime).count()<<"\n";
}
