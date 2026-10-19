// Six-row tail resynthesis: delete state 255, freely synthesize 75/112/131.
// Bounded fixtures are discovery gates, not an unbounded correctness proof.
#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <iostream>
#include <chrono>
#include <cstdint>
#include <algorithm>
#include <cstdlib>
using namespace std;
struct Row { int w,d,q; };
struct Conf {int q,h; array<uint64_t,8> a{};};
struct Case {Conf start, goal;};
array<array<Row,2>,256> tab;
vector<Case> cases;
vector<Row> acts;
vector<pair<int,int>> holes;
unsigned long long nodes=0,checks=0;
int maxcase=0, horizon=250;
chrono::steady_clock::time_point began;
double secondsLimit=600;
string output;
bool get(const Conf &c,int h){int p=h+128;return p>=0&&p<512?((c.a[p>>6]>>(p&63))&1):0;}
void put(Conf &c,int h,int v){int p=h+128;if(p>=0&&p<512){uint64_t b=1ULL<<(p&63);if(v)c.a[p>>6]|=b;else c.a[p>>6]&=~b;}}
bool same(const Conf& c,const Conf& g){return c.q==g.q&&c.h==g.h&&c.a==g.a;}
vector<int> blocks(vector<int> vs){vector<int> b;for(int v:vs){b.push_back(0);for(int i=0;i<v+1;i++)b.push_back(1);}return b;}
Conf paint(int q,int h,vector<int> right,vector<int> left,int origin){Conf c;c.q=q;c.h=h;for(int i=0;i<(int)right.size();i++)put(c,origin+i,right[i]);for(int i=0;i<(int)left.size();i++)put(c,origin-i-1,left[i]);return c;}
void makecases(bool homogeneous){
 vector<vector<int>> inputs={vector<int>(10,0),vector<int>(10,1),{0,1,2,0,3,1,0,1,0,2},{2,0,1,2,0,1,2,0,1,0,3}};
 for(auto vs:inputs)for(int r:{0,1,4,8})for(int mode:{0,1,2}){
  if(homogeneous)for(int i=9;i<(int)vs.size();i++)vs[i]=1;
  auto v=vs;if(mode==0)v[r]=0;if(mode==1)v[r]=max(1,v[r]);
  auto want=v;if(mode==1)--want[r];if(mode==2){++want[r];want.push_back(1);}
  auto marked=blocks(v);int k=1;for(int i=0;i<r;i++)k+=v[i]+2;marked[k]=0;
  cases.push_back({paint(mode==2?73:95,0,marked,{1,0,1},0),paint(mode==0?112:48,mode==1?0:-1,blocks(want),mode==1?vector<int>{1,1,0,1}:vector<int>{1,0,1},mode==1?1:0)});
 }
 swap(cases[0],cases[1]);
}
// Return -1 for success, -2 for finite rejection, or 2*q+bit for a hole.
int run(const Case& e){++checks;Conf c=e.start;for(int tick=0;tick<horizon;tick++){
 if(tick&&same(c,e.goal))return -1;
 if(c.q==254||c.q==255||c.h < -128||c.h>=384)return -2;
 int b=get(c,c.h);Row r=tab[c.q][b];if(r.q==-1)return 2*c.q+b;
 put(c,c.h,r.w);c.h+=r.d;c.q=r.q;
 }return -2;}
void dump(string name,int progress){ofstream f(output+name);f<<"{\n \"fixture_prefix_passed\": "<<progress<<",\n \"rows\": [\n";bool first=true;for(auto[q,b]:holes){if(!first)f<<",\n";first=false;auto r=tab[q][b];f<<"  ["<<q<<", "<<b<<", "<<r.w<<", "<<r.d<<", "<<r.q<<"]";}f<<"\n ]\n}\n";}
void visit(int i){++nodes;if(nodes%1000000==0){double sec=chrono::duration<double>(chrono::steady_clock::now()-began).count();cerr<<"nodes "<<nodes<<" maxcase "<<maxcase<<" seconds "<<sec<<endl;if(sec>secondsLimit)throw 1;}
 while(i<(int)cases.size()){
  int a=run(cases[i]);if(a==-2)return;
  if(a==-1){++i;if(i>maxcase){maxcase=i;dump("best.json",i);cerr<<"PROGRESS "<<i<<" nodes "<<nodes<<endl;}continue;}
  int q=a/2,b=a%2;for(auto r:acts){tab[q][b]=r;visit(i);}tab[q][b].q=-1;return;
 }
 dump("solution.json",i);cout<<"SOLUTION nodes "<<nodes<<endl;throw 2;
}
int main(int argc,char**argv){if(argc<3){cerr<<"usage: pulse6 table output_prefix [target_level] [seconds]";return 1;}
 ifstream f(argv[1]);string l;while(getline(f,l)){if(l.empty()||l[0]=='#')continue;istringstream in(l);int q,b,w,t;char d;in>>q>>b>>w>>d>>t;tab[q][b]={w,d=='R'?1:-1,t};}
 output=argv[2];int level=argc>3?atoi(argv[3]):0;secondsLimit=argc>4?atof(argv[4]):600;
 vector<int> targets={48,63,75,95,109,112,131,73,83};if(level==1)targets={2,4,6,7,10,14,20,28,31,38,40,44,48,56,60,63,64,69,73,75,83,95,109,112,131};if(level==2){targets.clear();for(int q=0;q<254;q++)if(q!=0&&q!=1&&q!=3&&q!=5&&q!=8&&q!=43&&q!=59&&q!=85&&q!=97)targets.push_back(q);}
 for(int q:targets)for(int w:{0,1})for(int d:{-1,1})acts.push_back({w,d,q});
 makecases(true);
 // Exact finite positive control under the same endpoint horizon.
 for(const auto& c:cases){Conf s=c.start;bool ok=false;for(int k=0;k<horizon;k++){if(k&&same(s,c.goal)){ok=true;break;}auto r=tab[s.q][get(s,s.h)];put(s,s.h,r.w);s.h+=r.d;s.q=r.q;}if(!ok){cerr<<"baseline failed\n";return 1;}}
 for(int q:{75,112,131})for(int b:{0,1}){holes.push_back({q,b});tab[q][b].q=-1;}
 began=chrono::steady_clock::now();int status=0;try{visit(0);}catch(int i){status=i;}
 double sec=chrono::duration<double>(chrono::steady_clock::now()-began).count();ofstream out(output+"result.json");out<<"{\"status\": \""<<(status==0?"COMPLETE":status==1?"TIME_LIMIT":"SOLUTION")<<"\", \"nodes\": "<<nodes<<", \"checks\": "<<checks<<", \"maxcase\": "<<maxcase<<", \"seconds\": "<<sec<<", \"actions_per_row\": "<<acts.size()<<", \"fixture_count\": "<<cases.size()<<", \"horizon\": "<<horizon<<"}\n";
 cout<<"status "<<status<<" nodes "<<nodes<<" maxcase "<<maxcase<<" seconds "<<sec<<endl;
}
