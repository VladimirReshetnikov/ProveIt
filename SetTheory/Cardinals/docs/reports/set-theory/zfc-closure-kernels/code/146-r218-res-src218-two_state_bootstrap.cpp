// Resynthesize both rows of two retained states without deleting a state.
// Every known initialized window must reach a positive unchanged-trajectory
// endpoint, restoring every represented cell. Enumerate ALL bounded solutions,
// and separately test blank startup against the general clean logical seeds.
// A window-neutral/blank hit still requires a fresh universal runtime proof.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Row { int w,d,z; };
struct Goal { int q,h,t; };
struct Case { int q,t; vector<Goal> goals; };

int main(int argc,char**argv) {
 if(argc<5){cerr<<"table windows stateA stateB [R=7] [new=96] [old=25] [seconds=240] [boot=3000000] [allstarts=0]\n";return 2;}
 int qa=stoi(argv[3]),qb=stoi(argv[4]);
 int R=argc>5?stoi(argv[5]):7,MS=argc>6?stoi(argv[6]):96,OS=argc>7?stoi(argv[7]):25;
 double budget=argc>8?stod(argv[8]):240;
 long long boot_bound=argc>9?stoll(argv[9]):3000000;
 bool allstarts=argc>10?stoi(argv[10])!=0:false;
 int N=2*R+1,B=1<<N;
 if(R<1||R>14)return 2;
 vector<array<Row,2>>T(2048);set<int>qs;string line;
 ifstream tf(argv[1]);
 while(getline(tf,line)){
  if(line.empty()||line[0]=='#')continue;
  stringstream ss(line);int q,b,w,z;char d;
  if(!(ss>>q>>b>>w>>d>>z)||q<0||q>=2048||b<0||b>1)return 2;
  T[q][b]={w,d=='R'?1:-1,z};qs.insert(q);
 }
 if(!qs.count(qa)||!qs.count(qb)||qa==qb)return 2;
 vector<Case>cases;array<int,2>counts{};
 ifstream wf(argv[2]);
 while(getline(wf,line)){
  if(line.empty()||line[0]=='#')continue;
  stringstream ss(line);int q,x;
  if(!(ss>>q>>x)||!qs.count(q)||x<0||x>=B)return 2;
  if(q!=qa&&q!=qb)continue;
  counts[q==qa?0:1]++;
  Case ca{q,x,{}};int oq=q,h=R,t=x;
  for(int n=0;n<OS;n++){
   if(h<0||h>=N||!qs.count(oq))break;
   auto row=T[oq][(t>>h)&1];t=(t&~(1<<h))|(row.w<<h);h+=row.d;oq=row.z;
   ca.goals.push_back({oq,h,t});
  }
  cases.push_back(move(ca));
 }
 for(int c:counts)if(!c)return 2;
 vector<Row>A;
 for(int w:{0,1})for(int d:{-1,1}){
  for(int z:qs)A.push_back({w,d,z});
  A.push_back({w,d,254});
 }
 auto start=chrono::steady_clock::now();
 auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 long long choices=0,checks=0,nodes=0,hits=0,boot_tests=0,boot_hits=0;bool timeout=false;
 array<Row,4>rows{};
 auto modified=[&](int q,int b){return q==qa?rows[b]:q==qb?rows[b+2]:T[q][b];};
 auto verify=[&](int known)->bool{
  for(const auto&ca:cases){
   int q=ca.q,h=R,t=ca.t;bool met=false;
   for(int n=0;n<MS;n++){
    if(h<0||h>=N||!qs.count(q))break;
    int b=(t>>h)&1,ri=q==qa?b:q==qb?b+2:-1;
    if(ri>=0&&!(known&(1<<ri))){met=true;break;}
    checks++;
    Row row=ri>=0?rows[ri]:T[q][b];
    t=(t&~(1<<h))|(row.w<<h);h+=row.d;q=row.z;
    for(auto g:ca.goals)if((q==254&&g.q==254)||(q==g.q&&h==g.h&&t==g.t)){met=true;break;}
    if(met)break;
   }
   if(!met)return false;
  }
  return true;
 };
 auto print_rows=[&](){for(int i=0;i<4;i++)cout<<" row"<<i<<" "<<rows[i].w<<" "<<rows[i].d<<" "<<rows[i].z;};
 auto boot=[&](int initial){
  boot_tests++;
  const int width=262144,origin=width/2;
  vector<unsigned char>t(width);set<int>ones;int q=initial,h=origin;
  set<tuple<int,int,unsigned long long>>small_seen;
  for(long long n=0;n<boot_bound;n++){
   if(!qs.count(q)||h<2||h>=width-2)return;
   if(q==84&&ones.size()>=11&&*ones.begin()==h-1){
    auto it=ones.upper_bound(h-1);
    if(it!=ones.end()&&*it>=h+64){
     int header=*it,cursor=header+1;vector<int>values;bool valid=true;
     while(cursor<=*ones.rbegin()){
      if(cursor+1>=width||t[cursor]||!t[cursor+1]){valid=false;break;}
      int count=0;cursor++;
      while(cursor<width&&t[cursor]){count++;cursor++;}
      values.push_back(count-1);
     }
     if(valid&&values.size()>=10){
      // Physical positions0,2,4,5,7,8 correspond to logical2,1,3,7,5,6.
      for(int i:{0,2,4,5,7,8})if(values[i]!=0)valid=false;
      if(valid){
       boot_hits++;cout<<"BOOT_HIT pair "<<qa<<" "<<qb<<" start "<<initial<<" steps "<<n<<" head "<<h-origin
         <<" gap "<<header-h-64<<" logical "<<values[6]<<" 0 0 0 "<<values[3]<<" 0 0 0 "<<values[1]
         <<" spares "<<values.size()-9;print_rows();cout<<" one_cells";
       for(int p:ones)cout<<" "<<p-origin;cout<<"\n"<<flush;return;
      }
     }
    }
   }
   // Exact cycle modulo translation for tapes supported on at most63 cells.
   // Both machine rules and the complete-frame acceptance predicate are
   // translation invariant, so a repeated normalized configuration is final.
   if(ones.empty()){
    if(!small_seen.insert({q,0,0}).second)return;
   }else if(*ones.rbegin()-*ones.begin()<63){
    int lo=*ones.begin();unsigned long long mask=0;
    for(int p:ones)mask|=1ULL<<(p-lo);
    if(!small_seen.insert({q,h-lo,mask}).second)return;
   }
   Row a=modified(q,t[h]);
   if(!t[h]&&a.z==q&&(ones.empty()||(a.d==1?h>*ones.rbegin():h<*ones.begin())))return;
   if(a.w){t[h]=1;ones.insert(h);}else{t[h]=0;ones.erase(h);}
   h+=a.d;q=a.z;
  }
 };
 array<vector<Row>,4>domains;
 for(int ri=0;ri<4;ri++)for(auto action:A){
  choices++;rows[ri]=action;
  if(verify(1<<ri))domains[ri].push_back(action);
 }
 array<int,4>order{0,1,2,3};
 sort(order.begin(),order.end(),[&](int a,int b){return domains[a].size()<domains[b].size();});
 cerr<<"domains";for(auto&d:domains)cerr<<" "<<d.size();cerr<<" order";for(auto x:order)cerr<<" "<<x;
 cerr<<" cases "<<cases.size()<<" seconds "<<elapsed()<<"\n";
 auto search=[&](auto&&self,int depth,int known)->void{
  if(timeout)return;
  if((++nodes&1023)==0&&elapsed()>budget){timeout=true;return;}
  if(depth==4){
   hits++;cout<<"NEUTRAL pair "<<qa<<" "<<qb;print_rows();cout<<"\n"<<flush;
   if(allstarts){for(int initial:qs)boot(initial);}
   else {boot(0);if(qa!=0)boot(qa);if(qb!=0)boot(qb);}
   if(elapsed()>budget)timeout=true;
   return;
  }
  int ri=order[depth];
  for(auto action:domains[ri]){
   rows[ri]=action;choices++;
   if((choices&4095)==0&&elapsed()>budget){timeout=true;return;}
   if(verify(known|(1<<ri)))self(self,depth+1,known|(1<<ri));
   if(timeout)return;
  }
 };
 search(search,0,0);
 cerr<<"status "<<(timeout?"INCOMPLETE_TIMEOUT":"COMPLETED")<<" choices "<<choices<<" nodes "<<nodes
     <<" checks "<<checks<<" neutral_hits "<<hits<<" boot_tests "<<boot_tests<<" boot_hits "<<boot_hits
     <<" seconds "<<elapsed()<<" old_bound "<<OS<<" new_bound "<<MS<<" boot_bound "<<boot_bound<<"\n";
}
