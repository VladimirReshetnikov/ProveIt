// Two-row blank-bootstrap discovery. A hit is only a finite frame witness.
#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,z;};
struct Sim{vector<unsigned char>t;set<int>ones;int q=0,h=32768;long long n=0;Sim():t(65536){};};
array<array<Row,2>,512>T;set<int> states;
int qa=66,ba=0,qb=198,bb=0;long long bound=3000000;int hits=0;
vector<int> wanted{0,0,0,3,0,0,3,0,0};
bool frame(Sim const&s,vector<int>&vals,int&gap){
 if(s.q!=84||s.ones.size()<11||*s.ones.begin()!=s.h-1)return false;
 auto it=s.ones.upper_bound(s.h-1);if(it==s.ones.end()||*it<s.h+64)return false;
 gap=*it-s.h-64;int c=*it+1;vals.clear();
 while(c<=*s.ones.rbegin()){
  if(c+1>=65536||s.t[c]||!s.t[c+1])return false;int count=0;c++;
  while(c<65536&&s.t[c]){count++;c++;}vals.push_back(count-1);
 }
 return vals.size()>=10&&vals[0]==0&&vals[2]==0&&vals[4]==0&&vals[5]==0&&vals[7]==0&&vals[8]==0;
}
// 1 exact clean frame; 2 first unknown second row; 0 rejected/bounded.
int run(Sim&s,bool pending){
 for(;s.n<bound;s.n++){
  if(!states.count(s.q)||s.h<2||s.h>=65534)return 0;
  vector<int>v;int gap;if(frame(s,v,gap))return 1;
  int b=s.t[s.h];if(pending&&s.q==qb&&b==bb)return 2;
  Row r=T[s.q][b];
  if(!b&&r.z==s.q&&(s.ones.empty()||(r.d==1?s.h>*s.ones.rbegin():s.h<*s.ones.begin())))return 0;
  if(r.w){s.t[s.h]=1;s.ones.insert(s.h);}else{s.t[s.h]=0;s.ones.erase(s.h);}
  s.h+=r.d;s.q=r.z;
 }return 0;
}
void hit(Sim const&s,Row a,Row b){
 vector<int>v;int gap;assert(frame(s,v,gap));hits++;
 cout<<"HIT "<<qa<<" "<<ba<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" ; "<<qb<<" "<<bb<<" "<<b.w<<" "<<b.d<<" "<<b.z<<" steps "<<s.n<<" head "<<s.h-32768<<" gap "<<gap<<" values";for(int x:v)cout<<" "<<x;cout<<" ones";for(int x:s.ones)cout<<" "<<x-32768;cout<<"\n"<<flush;
}
int main(int argc,char**argv){
 if(argc<2)return 2;if(argc>2)qa=atoi(argv[2]);if(argc>3)ba=atoi(argv[3]);if(argc>4)qb=atoi(argv[4]);if(argc>5)bb=atoi(argv[5]);if(argc>6)bound=atoll(argv[6]);
 ifstream in(argv[1]);string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};states.insert(q);}
 Row oldb=T[qb][bb];vector<Row>actions;for(int w:{0,1})for(int d:{-1,1})for(int z:states)actions.push_back({w,d,z});long long trials=0,pending=0;int outer=0;
 for(Row a:actions){outer++;T[qa][ba]=a;T[qb][bb]=oldb;Sim s;int r=run(s,true);
  if(r==1)hit(s,a,oldb);
  else if(r==2){pending++;for(Row b:actions){T[qb][bb]=b;Sim c=s;trials++;if(run(c,false)==1)hit(c,a,b);}}
  if(outer%20==0)cerr<<"PROGRESS "<<outer<<" pending "<<pending<<" trials "<<trials<<" hits "<<hits<<"\n"<<flush;
 }
 cerr<<"DONE outer "<<outer<<" pending "<<pending<<" trials "<<trials<<" hits "<<hits<<"\n";
}
