#include <array>
#include <vector>
#include <algorithm>
#include <random>
#include <chrono>
#include <fstream>
#include <iostream>
#include <cmath>
#include <set>
using namespace std;

// Seven working states, exits 7=old4 and 8=old84. All nine inputs are finite
// cylinders: an active read outside the known interval fails immediately.
// Short k has a one at -k and at 2; known intervening cells zero. Long has
// known zeros at -8..1 and a one at 2. Exterior cells are never assumed zero.
struct Row {int w,d,q;};
using Tab=array<Row,14>;
struct Eval {int score,pass; array<int,9> each;};
mt19937_64 rng(0x73aa2d6711ULL);
int ri(int n){return int(rng()%n);}
bool borrowed=false;
Row randomrow(){return {ri(2),ri(2)?1:-1,ri(borrowed?10:9)};}
int scorecase(const Tab&t,int k,int fuel){
 int lo=k==8?-8:-k; int h=0,q=0;
 unsigned initial=1u<<10; if(k<8) initial|=1u<<(8-k);
 unsigned tape=initial;
 array<array<unsigned,11>,7> seen{}; // only a soft diagnostic loop memo below
 int visited=0;
 int short_exit=borrowed?8:7,long_exit=borrowed?9:8;
 for(int n=0;n<fuel;n++){
  int broken=__builtin_popcount(tape^initial);
  if(k<8&&q==short_exit&&h==-k-1&&broken==0)return 0;
  if(k==8&&q==long_exit&&h>=-8&&h<=1&&broken==0)return 0;
  if(q>=7&&!borrowed)break;
  if(h<lo||h>2) return 80 + 3*abs(h-(h<lo?lo:2)) + __builtin_popcount(tape^initial)*3;
  visited=max(visited,-h);
  int bit=(tape>>(h+8))&1;
  Row a;
  if(q<7)a=t[2*q+bit];
  else if(q==7)a={bit,-1,bit?8:7}; // old2
  else if(q==8)a={bit,-1,bit?8:0}; // old4, entering local0=old6
  else if(q==9)a={bit,1,bit?10:9}; // old84
  else break;
  if(a.w)tape|=1u<<(h+8);else tape&=~(1u<<(h+8));
  h+=a.d;q=a.q;
 }
 int broken=__builtin_popcount(tape^initial);
 if(k<8){
  if(q==short_exit&&h==-k-1&&broken==0)return 0;
  int dist=abs(h+k+1);
  return 12*broken+4*min(dist,15)+(q==short_exit?0:q==long_exit?50:70)+1;
 }else{
  if(q==long_exit&&h>=-8&&h<=1&&broken==0)return 0;
  int dist=h>1?h-1:h< -8?-8-h:0;
  return 12*broken+4*min(dist,15)+(q==long_exit?0:q==short_exit?50:70)+1;
 }
}
Eval evaluate(const Tab&t,int fuel){
 Eval e{0,0,{}};
 for(int k=0;k<9;k++){int s=scorecase(t,k,fuel);e.each[k]=s;e.score+=s;e.pass+=(s==0);}
 return e;
}
void dump(const Tab&t,const Eval&e,string path){
 ofstream f(path);f<<"{\"working_states\":7,\"score\":"<<e.score<<",\"passed_contracts\":"<<e.pass<<",\"rows\":[";
 for(int j=0;j<14;j++){auto a=t[j];if(j)f<<",";f<<"["<<j/2<<","<<j%2<<","<<a.w<<",\""<<(a.d==1?"R":"L")<<"\","<<a.q<<"]";}
 f<<"],\"borrowed_existing_states\":"<<(borrowed?"true":"false")<<",\"case_scores\":[";for(int k=0;k<9;k++){if(k)f<<",";f<<e.each[k];}f<<"]}\n";
}
Tab folded(int dead,int keep,bool alternate){
 const array<Row,16> old=alternate?array<Row,16>{{
  {0,-1,1},{1,-1,8},{0,-1,2},{1,-1,8},{0,-1,3},{1,1,3},{0,-1,6},{1,1,3},
  {0,-1,5},{1,1,4},{0,-1,7},{1,-1,8},{0,-1,4},{1,1,0},{0,1,9},{1,-1,8}
 }}:array<Row,16>{{
  {0,-1,1},{1,-1,8},{0,-1,2},{1,-1,8},{0,-1,3},{1,-1,8},{0,-1,4},{1,-1,8},
  {0,-1,5},{1,-1,8},{0,-1,6},{1,-1,8},{0,-1,7},{1,-1,8},{0,1,9},{1,-1,8}
 }};
 array<int,10> mp{};int cur=0;
 int entry=dead==0?keep:0;mp[entry]=cur++;
 for(int q=0;q<8;q++)if(q!=dead&&q!=entry)mp[q]=cur++;
 mp[dead]=mp[keep];mp[8]=borrowed?8:7;mp[9]=borrowed?9:8;
 Tab t;
 for(int q=0;q<8;q++)if(q!=dead)for(int b=0;b<2;b++){
  Row a=old[2*q+b];a.q=mp[a.q];t[2*mp[q]+b]=a;
 }
 return t;
}
int main(int argc,char**argv){
 double seconds=argc>1?stod(argv[1]):120;int fuel=argc>2?stoi(argv[2]):96;
 string path=argc>3?argv[3]:"detector_best.json";
 borrowed=argc>4&&string(argv[4])=="borrowed";
 auto start=chrono::steady_clock::now();
 auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 vector<pair<int,Tab>> pool;
 Tab best{};Eval be{99999,0,{}};long long evaluated=0;
 auto examine=[&](const Tab&t){
  Eval e=evaluate(t,fuel);evaluated++;
  if(e.score<be.score){be=e;best=t;dump(t,e,path);cerr<<"best "<<e.score<<" pass "<<e.pass<<" checks "<<evaluated<<" sec "<<elapsed()<<"\n";}
  return e;
 };
 for(bool alt:{false,true})for(int dead=0;dead<8;dead++)for(int keep=0;keep<8;keep++)if(dead!=keep){
  Tab t=folded(dead,keep,alt);auto e=examine(t);pool.emplace_back(e.score,t);
 }
 // Parallel state-merging and independent replacement of the retained rows.
 for(int si=0;si<112;si++){
  const Tab seed=pool[si].second;
  int targets=borrowed?10:9;
  for(int q=0;q<7;q++)for(int a=0;a<4*targets;a++)for(int b=0;b<4*targets;b++){
   Tab t=seed;t[2*q]={a/(2*targets),(a/targets)%2?1:-1,a%targets};t[2*q+1]={b/(2*targets),(b/targets)%2?1:-1,b%targets};
   Eval e=examine(t);if(e.score==0){cout<<"SAT "<<evaluated<<"\n";return 0;}
   if(e.score<=be.score+12)pool.emplace_back(e.score,t);
  }
  if(elapsed()>seconds)break;
 }
 sort(pool.begin(),pool.end(),[](auto&a,auto&b){return a.first<b.first;});if(pool.size()>256)pool.resize(256);
 for(long long restart=0;elapsed()<seconds;restart++){
  Tab current=restart%7==0?best:pool[ri(min<int>(pool.size(),restart%5?32:256))].second;
  Eval ce=evaluate(current,fuel);double temp=2.0+ri(4000)/100.0;
  for(int it=0;it<4000 && elapsed()<seconds;it++){
   Tab t=current;int changes=(it%241==0?2+ri(3):1);
   for(int c=0;c<changes;c++){int j=ri(14);t[j]=randomrow();}
   Eval e=examine(t);if(e.score==0){cout<<"SAT "<<evaluated<<"\n";return 0;}
   int diff=e.score-ce.score;
   if(diff<=0||double(rng()%1000000)/1000000.0<exp(-diff/temp)){current=t;ce=e;}
   if(e.score<=be.score+8 && it%43==0){pool.emplace_back(e.score,t);if(pool.size()>512){sort(pool.begin(),pool.end(),[](auto&a,auto&b){return a.first<b.first;});pool.resize(256);}}
  }
 }
 dump(best,be,path);cout<<"NO_HIT best_score="<<be.score<<" passed="<<be.pass<<" evaluated="<<evaluated<<" seconds="<<elapsed()<<"\n";
}
