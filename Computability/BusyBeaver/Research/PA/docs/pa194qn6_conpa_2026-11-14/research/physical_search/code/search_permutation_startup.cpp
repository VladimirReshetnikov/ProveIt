// Search literal blank initializations after one prescribed row edit.
// Clean-seed detection checks the WHOLE finite support, any translation and
// padding >=48, template-defined register constraints, and nonempty arbitrary
// spares. The any-frame templates allow all nine register values.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};
int main(int argc,char**argv){
 if(argc<4){cerr<<"table edits.tsv maxSteps [first_edit last_edit]\n";return 2;}
 int bound=stoi(argv[3]),lo=argc>4?stoi(argv[4]):0,hi=argc>5?stoi(argv[5]):INT_MAX;
 struct Seed{int pc;string path;int arbitrary;};vector<Seed>seeds;
 if(argc>6){ifstream sf(argv[6]);Seed s;while(sf>>s.pc>>s.path>>s.arbitrary)seeds.push_back(s);}
 else seeds.push_back({25,"100000",74});
 array<A,2>base[3000],row[3000];bool ex[3000]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char dir;
 while(f>>q>>b>>w>>dir>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]={w,dir=='R'?1:-1,n};}
 struct Edit{int id,q,b,w,d,n;};vector<Edit>edits;ifstream e(argv[2]);Edit ed;
 while(e>>ed.id>>ed.q>>ed.b>>ed.w>>ed.d>>ed.n)if(ed.id>=lo&&ed.id<hi)edits.push_back(ed);
 int successes=0;long long simulations=0,ticks=0,halts=0,rays=0,limits=0;auto t0=chrono::steady_clock::now();
 vector<int> perm{0,1,2,3,4,5,6,7,8};
 vector<int> skips{51,36,25,48,32,33,22,55,60};
 vector<vector<int>> entry{{56},{39},{41,61},{144},{17,161},{82},{14},{45},{21}};
 long long perms=0;
 do {
  Edit ed{int(perms++),-1,0,0,0,0};
  for(int q:qs)row[q]=base[q];
  for(int j=0;j<9;j++)for(int q:entry[j])row[q][1].n=skips[perm[j]];
  int raydir[3000]={};
  for(int q:qs){int r=q,d=0;set<int>seen;
   while(r>=0&&r<3000&&ex[r]&&!seen.count(r)){seen.insert(r);A a=row[r][0];if(d&&a.d!=d){d=0;break;}d=a.d;r=a.n;}
   if(d&&seen.count(r))raydir[q]=d;
  }
  for(int start:vector<int>{74}){simulations++;int q=start,h=0;set<int>ones;bool ended=false;
   for(int st=0;st<=bound;st++){
    if(q==254){halts++;ended=true;break;}
    if(q==84&&ones.size()>=13){for(Seed seed:seeds){
     vector<int>x(ones.begin(),ones.end());vector<int>prefix{h-1};for(size_t j=0;j<seed.path.size();j++)if(seed.path[j]=='1')prefix.push_back(h+j);
     size_t m=prefix.size();bool ok=x.size()>m&&equal(prefix.begin(),prefix.end(),x.begin())&&x[m]>=h+48;int gap=ok?x[m]-h-48:-1;
     if(!ok)continue;
     vector<int>values;size_t i=m+1;int pos=x[m];
     while(ok&&i<x.size()){if(x[i]!=pos+2){ok=false;break;}int len=1;pos=x[i++];while(i<x.size()&&x[i]==pos+1){len++;pos=x[i++];}values.push_back(len-1);}
     if(values.size()<10)ok=false;
     for(int j=0;ok&&j<9;j++)if(!(seed.arbitrary>>j&1)){
      int v=values[j];
      // Optional stronger semantic seed: PA-provable tiny formula codes.
      // These finite admissible sets are justified in the separate theory note.
      if(j==0){if(v!=0&&v!=3&&v!=6&&v!=10)ok=false;}
      else if(j==2||j==7){if(v!=0&&v!=2&&v!=3&&v!=4)ok=false;}
      else if(v!=0)ok=false;
     }
     if(ok){successes++;cout<<"{\"edit\":"<<ed.id<<",\"row\":["<<ed.q<<","<<ed.b<<"],\"action\":["<<ed.w<<","<<ed.d<<","<<ed.n<<"],\"start\":"<<start<<",\"steps\":"<<st<<",\"head\":"<<h<<",\"pc\":"<<seed.pc<<",\"gap\":"<<gap<<",\"values\":[";
      for(size_t j=0;j<values.size();j++){if(j)cout<<',';cout<<values[j];}cout<<"],\"ones\":[";for(size_t j=0;j<x.size();j++){if(j)cout<<',';cout<<x[j];}cout<<"]}"<<endl;ended=true;break;}
    }if(ended)break;}
    if(st==bound||abs(h)>20000||ones.size()>20000){limits++;ended=true;break;}
    bool bit=ones.count(h);int rd=raydir[q];
    if(!bit&&rd&&((rd==1&&(ones.empty()||*ones.rbegin()<h))||(rd==-1&&(ones.empty()||*ones.begin()>h)))){rays++;ended=true;break;}
    A a=row[q][bit];if(a.w)ones.insert(h);else ones.erase(h);h+=a.d;q=a.n;ticks++;
   }
  }
  if(perms%10000==0) cerr<<"PERMS "<<perms<<" successes "<<successes<<" simulations "<<simulations<<" ticks "<<ticks<<"\n";
 } while(next_permutation(perm.begin(),perm.end()));
 cerr<<"DONE permutations "<<perms<<" successes "<<successes<<" simulations "<<simulations<<" ticks "<<ticks<<" halts "<<halts<<" rays "<<rays<<" limits "<<limits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
}
