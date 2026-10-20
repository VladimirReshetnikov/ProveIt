// Own bounded blank-start discovery; no claim follows from a failed finite scan.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Action { int write=-1, move=0, next=-1; };
using Tape=set<long long>;
struct Frame { bool valid=false,accepted=false,clean=false;long long gap=0;vector<long long> logical,spares; };
Frame frame(long long h,const Tape& ones) {
 Frame f;if(ones.size()<2 || *ones.begin()!=h-1)return f;
 auto it=next(ones.begin());long long header=*it;
 if(header<h+64)return f;
 ++it;long long p=header+1;vector<long long> values;
 while(it!=ones.end()) {
  if(*it!=p+1)return f;
  long long first=*it,last=*it;++it;
  while(it!=ones.end() && *it==last+1){last=*it;++it;}
  values.push_back(last-first);p=last+1;
 }
 if(values.size()<10)return f;
 const array<int,9> phy={6,2,0,4,3,7,8,5,1};
 for(int k:phy)f.logical.push_back(values[k]);
 f.spares.assign(values.begin()+9,values.end());f.gap=header-h-64;f.valid=true;
 f.accepted=f.logical==vector<long long>({3,0,0,0,3,0,0,0,0});
 f.clean=true;for(int k:{1,2,3,5,6,7})if(f.logical[k]!=0)f.clean=false;
 return f;
}
template<class C>void arr(const C&xs){cout<<'[';bool first=true;for(auto x:xs){if(!first)cout<<',';cout<<x;first=false;}cout<<']';}
void emit_frame(const Frame& f,long long h,const Tape&ones,long long tick){cout<<"{\"steps\":"<<tick<<",\"head\":"<<h<<",\"gap\":"<<f.gap<<",\"logical\":";arr(f.logical);cout<<",\"spares\":";arr(f.spares);cout<<",\"ones\":";arr(ones);cout<<'}';}
int main(int argc,char**argv){
 if(argc!=6){cerr<<"table max_steps seconds first_start last_start\n";return 2;}
 array<array<Action,2>,512>T;set<int>states;ifstream input(argv[1]);string l;
 while(getline(input,l)) {if(l.empty()||l[0]=='#')continue;istringstream s(l);int q,b,w,z;char d;if(!(s>>q>>b>>w>>d>>z)||q<0||q>=512||b<0||b>1||w<0||w>1||(d!='L'&&d!='R')||z<0||z>=512||T[q][b].write!=-1)return 3;T[q][b]={w,d=='R'?1:-1,z};states.insert(q);}
 if(!input.eof()||states.empty()||states.count(254))return 4;
 for(int q:states)for(int b:{0,1})if(T[q][b].write<0||(T[q][b].next!=254&&!states.count(T[q][b].next)))return 5;
 long long cap=stoll(argv[2]);int seconds=stoi(argv[3]),lo=stoi(argv[4]),hi=stoi(argv[5]);if(cap<1||cap>1000000||seconds<1||seconds>110)return 6;
 auto began=chrono::steady_clock::now();int completed=0;bool wall=false;
 for(int start:states){if(start<lo||start>hi)continue;
  int q=start;long long h=0,tick=0;Tape ones;string status="STEP_BOUND";bool saved=false;
  cout<<"{\"start\":"<<start<<",\"first_other_clean_frame\":";
  string first_clean="null"; // Full first-clean frames are emitted separately when seen.
  cout<<"null,\"observations\":[";bool first_observation=true;
  for(;tick<=cap;++tick){
   if(tick%4096==0 && chrono::duration<double>(chrono::steady_clock::now()-began).count()>=seconds){status="WALL_BOUND";wall=true;break;}
   if(q==254){status="HALTED";break;}
   if(q==84){auto f=frame(h,ones);if(f.valid&&(f.accepted||(!saved&&f.clean))){if(!first_observation)cout<<',';emit_frame(f,h,ones,tick);first_observation=false;saved=true;if(f.accepted){status="ACCEPTED_SEED_FRAME";break;}}}
   if(tick==cap)break;
   int bit=ones.count(h);const auto&a=T[q][bit];
   // With scanned0 and a self-loop heading beyond every existing1,
   // each next scanned cell stays0. The one-row infinite-ray proof is exact.
   bool empty_ahead=a.move==1?ones.upper_bound(h)==ones.end():ones.lower_bound(h)==ones.begin();
   if(bit==0&&a.next==q&&empty_ahead){status="UNCONDITIONAL_ZERO_RAY";break;}
   if(a.write)ones.insert(h);else ones.erase(h);h+=a.move;q=a.next;
  }
  cout<<"],\"status\":\""<<status<<"\",\"steps\":"<<tick<<",\"state\":"<<q<<",\"head\":"<<h<<",\"ones_count\":"<<ones.size()<<",\"elapsed_seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<"}\n"<<flush;
  ++completed;if(wall)break;
 }
 cerr<<"completed="<<completed<<" wall="<<wall<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
 return wall?7:0;
}
