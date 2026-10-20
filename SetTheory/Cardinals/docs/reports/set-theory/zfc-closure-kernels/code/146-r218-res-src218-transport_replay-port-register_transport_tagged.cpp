// Candidate generator: transport direct selectors and retain tagged aliases.
// Successful blank runs are proposals only. Full symbolic source interfaces
// are required separately; no register-permutation compiler theorem is assumed.
#include <algorithm>
#include <array>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <unordered_set>
#include <vector>
using namespace std;
struct Row{int w,d,z;bool operator==(const Row&o)const{return w==o.w&&d==o.d&&z==o.z;}};
struct Role{int q,b,op,arg;};
const int CI[9]={14,61,56,161,71,63,13,82,39},CD[9]={14,41,56,17,144,45,21,62,39},PHY[9]={6,2,0,4,3,7,8,5,1};
struct Small{int q,h;uint64_t bits;bool operator==(const Small&o)const{return q==o.q&&h==o.h&&bits==o.bits;}};
struct Hash{size_t operator()(const Small&x)const{return x.bits*11400714819323198485ull ^ (uint64_t(x.q)<<40) ^ (uint64_t(x.h+65536)*0x9e3779b9);}};
int main(int argc,char**argv){
 if(argc<4)return 2;string line;array<array<Row,2>,2048>base{};set<int>states;
 ifstream input(argv[1]);while(getline(input,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;base[q][b]={w,d=='R'?1:-1,z};states.insert(q);}
 vector<Role>roles;ifstream ri(argv[2]);Role role;while(ri>>role.q>>role.b>>role.op>>role.arg)roles.push_back(role);
 filesystem::path out(argv[3]);filesystem::create_directories(out);
 long long bound=argc>4?stoll(argv[4]):3000000;int fixedstart=argc>5?stoi(argv[5]):0;
 set<string>only;if(argc>6){ifstream f(argv[6]);string s;while(f>>s)only.insert(s);}
 array<int,9>perm{0,1,2,3,4,5,6,7,8};long long tried=0,feasible=0,hits=0,bounded=0,ray=0,cycles=0,totalsteps=0;
 auto begun=chrono::steady_clock::now();ofstream log(out/"results.jsonl");
 do{
  string name;for(int x:perm)name+=char('0'+x);if(!only.empty()&&!only.count(name))continue;
  tried++;auto T=base;array<array<int,2>,2048>assigned{};for(auto&a:assigned)a={-1,-1};bool good=true;
  for(auto r:roles){int z=(r.op==0?CI:CD)[perm[r.arg]];int &a=assigned[r.q][r.b];if(a!=-1&&a!=z){good=false;break;}a=z;T[r.q][r.b]={r.b,1,z};}
  if(!good)continue;
  if(!(T[301][0]==T[30][0])||!(T[88][0]==Row{0,1,122})||!(T[88][1]==Row{1,1,103}))continue;
  feasible++;for(int q:states)for(int b=0;b<2;b++)if(T[q][b].z==301)T[q][b].z=88;
  T[88][0]={0,-1,51};T[88][1]={1,1,103};T[51][0]={0,1,122};T[51][1]={1,1,51};
  const int width=65536,origin=width/2;vector<unsigned char>t(width);set<int>ones;int q=fixedstart,h=origin;string reason="BOUND";long long n=0;vector<int>values;int gap=-1;unordered_set<Small,Hash>seen;
  for(;n<bound;n++){
   if(q==254||!states.count(q)){reason="HALT";break;}if(h<2||h>=width-2){reason="TAPE_SEARCH_LIMIT";break;}
   if(q==84&&ones.size()>=11&&*ones.begin()==h-1){
    auto it=ones.upper_bound(h-1);if(it!=ones.end()&&*it>=h+64){int header=*it,cursor=header+1;values.clear();bool valid=true;
     while(cursor<=*ones.rbegin()){if(cursor+1>=width||t[cursor]||!t[cursor+1]){valid=false;break;}int count=0;cursor++;while(cursor<width&&t[cursor]){count++;cursor++;}values.push_back(count-1);}
     if(valid&&values.size()>=10){for(int i=0;i<9;i++)if(i!=PHY[perm[0]]&&i!=PHY[perm[4]]&&i!=PHY[perm[8]]&&values[i]!=0)valid=false;
      if(valid){reason="HIT";gap=header-h-64;break;}}
    }
   }
   Row row=T[q][t[h]];
   if(!t[h]&&row.z==q&&(ones.empty()||(row.d==1?h>*ones.rbegin():h<*ones.begin()))){reason="BLANK_RAY";break;}
   if(ones.empty()||(*ones.rbegin()-*ones.begin()<=63)){
    int origin1=ones.empty()?h:*ones.begin();uint64_t bits=0;for(int x:ones)bits|=1ull<<(x-origin1);
    if(!seen.insert({q,h-origin1,bits}).second){reason="SMALL_EXACT_CYCLE";break;}
   }
   if(row.w){t[h]=1;ones.insert(h);}else{t[h]=0;ones.erase(h);}h+=row.d;q=row.z;
  }
  totalsteps+=n;if(reason=="BOUND")bounded++;if(reason=="BLANK_RAY")ray++;if(reason=="SMALL_EXACT_CYCLE")cycles++;
  if(reason=="HIT"){
   hits++;filesystem::path dir=out/name;filesystem::create_directories(dir);ofstream tm(dir/"candidate218.tm");
   for(int s:states)if(s!=301)for(int b=0;b<2;b++){auto a=T[s][b];tm<<s<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.z<<'\n';}
   ofstream seed(dir/"startup.json");seed<<"{\"status\":\"FINITE_COMPLETE_FRAME_HIT\",\"start\":"<<fixedstart<<",\"steps\":"<<n<<",\"head\":"<<h-origin<<",\"gap\":"<<gap<<",\"permutation\":[";
   for(int i=0;i<9;i++)seed<<(i?",":"")<<perm[i];seed<<"],\"physical_values\":[";for(size_t i=0;i<values.size();i++)seed<<(i?",":"")<<values[i];seed<<"],\"ones\":[";bool comma=false;for(int x:ones){seed<<(comma?",":"")<<x-origin;comma=true;}seed<<"]}\n";
   cout<<"HIT "<<name<<" steps "<<n<<" gap "<<gap<<" spares "<<values.size()-9<<"\n"<<flush;
  }
  if(reason=="HIT"||reason=="BOUND"||reason=="TAPE_SEARCH_LIMIT")log<<"{\"permutation\":\""<<name<<"\",\"reason\":\""<<reason<<"\",\"steps\":"<<n<<",\"state\":"<<q<<"}\n"<<flush;
  if(feasible%1000==0)cerr<<"tried "<<tried<<" feasible "<<feasible<<" hits "<<hits<<" bounded "<<bounded<<" rays "<<ray<<" cycles "<<cycles<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begun).count()<<"\n"<<flush;
 }while(next_permutation(perm.begin(),perm.end()));
 cerr<<"FINAL tried "<<tried<<" feasible "<<feasible<<" hits "<<hits<<" bounded "<<bounded<<" rays "<<ray<<" cycles "<<cycles<<" totalsteps "<<totalsteps<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begun).count()<<"\n";
}
