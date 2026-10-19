// Bounded synthesis of five jointly unknown rows with state 255 removed.
// The forward carry and reverse rollback laws are fixed; the tail/branch
// microcode is synthesized. Finite fixtures and finite clocks are explicit.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using Tape=std::array<uint64_t,4>;
struct Row{int w,d,t;};using Table=std::array<std::array<Row,2>,256>;
struct Case{int start,finish,head;Tape initial{},target{};};
bool get(const Tape&t,int h){return (t[h>>6]>>(h&63))&1;}
void set(Tape&t,int h,int b){uint64_t v=uint64_t(1)<<(h&63);if(b)t[h>>6]|=v;else t[h>>6]&=~v;}
Table table;std::vector<Case>cases;std::vector<std::pair<int,int>>unknown;
std::vector<Row>actions;uint64_t branches=0,solved=0,complete=0;int fuel=300;bool timedout=false;
std::chrono::steady_clock::time_point began;double seconds_limit=180;std::ofstream survivors;
struct Result{int kind,row;};
Result test(const Case&c){
 Tape a=c.initial;int h=32,q=c.start;
 for(int k=0;k<fuel;k++){
  if(k&&q==c.finish&&h==c.head+32&&a==c.target)return {1,-1};
  if(h<0||h>=256||q==254||q==255)return {0,-1};
  int bit=get(a,h);Row r=table[q][bit];
  if(r.t<0)return {2,int(-r.t-1)};
  set(a,h,r.w);h+=r.d;q=r.t;
 }
 return {0,-1};
}
void search(int ci,int depth){
 if(timedout)return;
 if((branches&65535)==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()>seconds_limit){timedout=true;return;}
 if(ci==int(cases.size())){
  solved++;survivors<<"candidate "<<solved<<" depth "<<depth;
  for(auto[q,b]:unknown){Row r=table[q][b];survivors<<" | "<<q<<' '<<b<<' '<<r.w<<' '<<r.d<<' '<<r.t;}
  survivors<<'\n';survivors.flush();return;
 }
 Result r=test(cases[ci]);
 if(!r.kind)return;
 if(r.kind==1){search(ci+1,depth);return;}
 auto[q,b]=unknown[r.row];Row missing=table[q][b];
 for(Row a:actions){table[q][b]=a;branches++;if(depth+1==int(unknown.size()))complete++;search(ci,depth+1);if(timedout)break;}
 table[q][b]=missing;
}
int main(int argc,char**argv){
 if(argc<3)return 2;std::ifstream in(argv[1]);int nr;in>>nr;
 for(int i=0;i<nr;i++){int q,b;Row r;in>>q>>b>>r.w>>r.d>>r.t;table[q][b]=r;}
 int nc;in>>nc;std::vector<Case>all(nc);
 for(auto&c:all){int n,x;in>>c.start>>c.finish>>c.head>>n;for(int i=0;i<n;i++){in>>x;set(c.initial,x+32,1);}in>>n;for(int i=0;i<n;i++){in>>x;set(c.target,x+32,1);}}
 // First expose one instance of each operation before larger list fixtures.
 for(int i:{0,1,8})cases.push_back(all[i]);for(int i=0;i<nc;i++)if(i!=0&&i!=1&&i!=8)cases.push_back(all[i]);
 unknown={{109,0},{75,0},{75,1},{131,0},{131,1}};
 if(argc>=5&&std::stoi(argv[4])>=7){unknown.push_back({112,0});unknown.push_back({112,1});}
 if(argc>=5&&std::stoi(argv[4])>=10){unknown.push_back({95,0});unknown.push_back({95,1});unknown.push_back({109,1});}
 for(int i=0;i<int(unknown.size());i++){auto[q,b]=unknown[i];table[q][b]={0,0,-i-1};}
 for(int w:{0,1})for(int d:{-1,1})for(int t:{95,109,75,131,112,48,63})actions.push_back({w,d,t});
 if(argc>=4)seconds_limit=std::stod(argv[3]);
 survivors.open(std::string(argv[2])+"-survivors.txt");began=std::chrono::steady_clock::now();search(0,0);
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
 uint64_t nominal=1;for(auto row:unknown)nominal*=28;
 std::ofstream report(std::string(argv[2])+"-summary.json");report<<"{\"branches\":"<<branches<<",\"complete_assignments_visited\":"<<complete<<",\"survivors\":"<<solved<<",\"completed\":"<<(!timedout?"true":"false")<<",\"nominal_assignments\":"<<nominal<<",\"actions_per_row\":28,\"unknown_rows\":"<<unknown.size()<<",\"macro_cases\":"<<nc<<",\"fuel\":"<<fuel<<",\"seconds\":"<<sec<<",\"finite_only\":true}\n";
 std::cout<<"branches "<<branches<<" full "<<complete<<" solved "<<solved<<" completed "<<!timedout<<" seconds "<<sec<<"\n";
}
