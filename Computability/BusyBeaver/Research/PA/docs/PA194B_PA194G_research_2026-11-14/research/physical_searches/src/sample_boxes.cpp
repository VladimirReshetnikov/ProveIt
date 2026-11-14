// Heuristic PREFIX sampling only: stop at the first return to native84.
// That can be an intermediate controller return within one source instruction.
// These samples do not replace the independent full symbolic source contracts.
#include <bits/stdc++.h>
using namespace std;
struct Act { int w,d,n; }; Act rows[3000][2];
set<int> boxes={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
set<int> pat[3000]; int K=4; long long ticks=0; int maxsteps=0;
void simulate(string path,vector<int> vals,bool blank=false) {
 vector<unsigned char> tape(8192);int origin=1024;
 if(!blank){tape[origin-1]=1;for(int i=0;i<(int)path.size();i++)tape[origin+i]=path[i]-'0';tape[origin+48]=1;int p=origin+49;for(int v:vals){p++;for(int j=0;j<=v;j++)tape[p++]=1;}}
 int q=blank?74:84,h=origin;int bound=blank?58242:200000;
 for(int step=0;step<bound;step++){
  if(q==254||(!blank&&step&&q==84)){maxsteps=max(maxsteps,step);return;}
  if(h<K||h+K>=(int)tape.size()){cerr<<"OUTSIDE"<<endl;exit(2);}
  if(boxes.count(q)) {int p=0;for(int j=-K;j<=K;j++)p|=tape[h+j]<<(j+K);pat[q].insert(p);}
  auto a=rows[q][tape[h]];tape[h]=a.w;h+=a.d;q=a.n;ticks++;
 }
 if(!blank){cerr<<"BOUND"<<endl;exit(3);}
}
int main(int argc,char**argv){
 ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n)rows[q][b]={w,d=='R'?1:-1,n};
 if(argc>3)K=stoi(argv[3]);
 ifstream sf(argv[2]);vector<string> paths;string p;int pc;while(sf>>pc>>p)paths.push_back(p);
 vector<vector<int>> values;
 for(int v:{0,1,2,3,8})values.push_back(vector<int>(12,v));
 for(int v:{1,2,8})for(int i=0;i<9;i++){vector<int>x(12,0);x[i]=v;values.push_back(x);x.assign(12,v);x[i]=0;values.push_back(x);}
 mt19937 gen(193);
 for(int j=0;j<20;j++){vector<int>x(12);for(auto&v:x)v=gen()%10;values.push_back(x);}
 int count=0;for(auto path:paths){for(auto vs:values)simulate(path,vs);if(++count%1000==0)cerr<<count<<" "<<ticks<<endl;}
 simulate({}, {},true);
 for(int q:boxes)for(int p:pat[q])cout<<q<<" "<<p<<"\n";
 long long cnt=0;for(int q:boxes)cnt+=pat[q].size();
 cerr<<"DONE frames "<<paths.size()*values.size()<<" ticks "<<ticks<<" contexts "<<cnt<<" maxsteps "<<maxsteps<<endl;
}
