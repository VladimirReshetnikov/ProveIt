// Bounded four-row synthesis.  Two old states are merged; a distinct helper
// retains its old role.  All rows of both resulting states are synthesized.
// Every original role window must reach a positive old-trajectory endpoint.
// Partial assignments stop at the first unspecified row.  Thus every pruning
// rejection is sound for this bounded whole-window family, but a timed-out run
// is explicitly incomplete.  Any hit requires independent certificate replay.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <cstdint>
using namespace std;
struct Row { int w,d,z; };
struct Goal { int q,h,t; };
struct Case { int q,t; vector<Goal> goals; };

int main(int argc,char**argv) {
 if(argc<6){cerr<<"table windows keep drop helpers_csv [R=7] [new=64] [old=25] [seconds=240]\n";return 2;}
 int keep=stoi(argv[3]),drop=stoi(argv[4]);
 vector<int>mutableq{keep};string helperword=argv[5];replace(helperword.begin(),helperword.end(),',',' ');stringstream hs(helperword);int hv;while(hs>>hv)mutableq.push_back(hv);
 int NR=2*mutableq.size();if(NR>16)return 2;
 vector<int>rix(2048,-1);for(int i=0;i<(int)mutableq.size();i++){if(mutableq[i]==drop||rix[mutableq[i]]>=0)return 2;rix[mutableq[i]]=2*i;}

 int R=argc>6?stoi(argv[6]):7,MS=argc>7?stoi(argv[7]):64,OS=argc>8?stoi(argv[8]):25;
 double budget=argc>9?stod(argv[9]):240;
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
 if(!qs.count(keep)||(drop>=0&&!qs.count(drop))||keep==drop)return 2;for(int q:mutableq)if(!qs.count(q))return 2;
 auto red=[&](int q){return q==drop?keep:q;};
 vector<Case>cases;vector<int>counts(mutableq.size()+1);
 ifstream wf(argv[2]);
 while(getline(wf,line)){
  if(line.empty()||line[0]=='#')continue;
  stringstream ss(line);int q,x;
  if(!(ss>>q>>x)||!qs.count(q)||x<0||x>=B)return 2;
  if(q!=drop&&rix[q]<0)continue;
  counts[q==drop?mutableq.size():rix[q]/2]++;
  Case ca{q,x,{}};int oq=q,h=R,t=x;
  for(int n=0;n<OS;n++){
   if(h<0||h>=N||!qs.count(oq))break;
   auto row=T[oq][(t>>h)&1];t=(t&~(1<<h))|(row.w<<h);h+=row.d;oq=row.z;
   ca.goals.push_back({red(oq),h,t});
  }
  cases.push_back(move(ca));
 }
 for(int i=0;i<(int)counts.size();i++)if(!counts[i]&&!(drop<0&&i+1==(int)counts.size()))return 2;
 vector<Row>A;
 for(int w:{0,1})for(int d:{-1,1}){
  for(int z:qs)if(z!=drop)A.push_back({w,d,z});
  A.push_back({w,d,254});
 }
 auto start=chrono::steady_clock::now();
 auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 long long choices=0,checks=0,nodes=0;int hits=0;bool timeout=false;
 vector<Row>rows(NR);
 auto verify=[&](int known)->bool{
  for(const auto&ca:cases){
   int q=red(ca.q),h=R,t=ca.t;bool met=false;
   for(int n=0;n<MS;n++){
    if(h<0||h>=N||!qs.count(q))break;
    int b=(t>>h)&1,ri=rix[q]>=0?rix[q]+b:-1;
    if(ri>=0&&!(known&(1<<ri))){met=true;break;}
    checks++;
    Row row=ri>=0?rows[ri]:T[q][b];
    t=(t&~(1<<h))|(row.w<<h);h+=row.d;q=red(row.z);
    for(auto g:ca.goals)if((q==254&&g.q==254)||(q==g.q&&h==g.h&&t==g.t)){met=true;break;}
    if(met)break;
   }
   if(!met)return false;
  }
  return true;
 };
 vector<vector<Row>>domains(NR);
 for(int ri=0;ri<NR;ri++)for(auto action:A){
  choices++;rows[ri]=action;
  if(verify(1<<ri))domains[ri].push_back(action);
 }
 if(argc>10&&(string(argv[10])=="keep_ones"||string(argv[10])=="keep_scanner_one"||string(argv[10])=="keep_decoder_one"||string(argv[10])=="keep_all_ones"||string(argv[10]).rfind("free_one_",0)==0)){
  vector<int>fixed=string(argv[10])=="keep_ones"?vector<int>{1,3}:string(argv[10])=="keep_scanner_one"?vector<int>{3}:vector<int>{1};
  if(string(argv[10])=="keep_all_ones"){fixed.clear();for(int ri=1;ri<NR;ri+=2)fixed.push_back(ri);}
  if(string(argv[10]).rfind("free_one_",0)==0){int fq=stoi(string(argv[10]).substr(9));fixed.clear();for(int ri=1;ri<NR;ri+=2)if(mutableq[ri/2]!=fq)fixed.push_back(ri);}
  for(int ri:fixed){Row wanted=T[mutableq[ri/2]][1];vector<Row>single;
    for(auto a:domains[ri])if(a.w==wanted.w&&a.d==wanted.d&&a.z==wanted.z)single.push_back(a);domains[ri]=single;
  }
 }
 vector<int>order(NR);for(int i=0;i<NR;i++)order[i]=i;
 sort(order.begin(),order.end(),[&](int a,int b){return domains[a].size()<domains[b].size();});
 cerr<<"domains";for(auto&d:domains)cerr<<" "<<d.size();cerr<<" order";for(auto x:order)cerr<<" "<<x;
 cerr<<" cases "<<cases.size()<<" seconds "<<elapsed()<<"\n";
 for(int ri=0;ri<NR;ri++){
  Row pref=T[mutableq[ri/2]][ri%2];
  if(mutableq[ri/2]==88&&ri%2==0)pref={0,-1,51};
  if(mutableq[ri/2]==51&&ri%2==0)pref={0,1,122};
  stable_sort(domains[ri].begin(),domains[ri].end(),[&](Row a,Row b){
    auto dist=[&](Row v){return 4*(v.z!=pref.z)+2*(v.d!=pref.d)+(v.w!=pref.w);};return dist(a)<dist(b);
  });
 }
 struct Pending{int ci,q,h,t,n;};
 vector<Pending>initial;
 for(int ci=0;ci<(int)cases.size();ci++)initial.push_back({ci,red(cases[ci].q),R,cases[ci].t,0});
 auto advance=[&](const vector<Pending>&input,vector<Pending>&output,int known)->bool{
  output.clear();output.reserve(input.size());
  for(auto p:input){
   bool met=false,blocked=false;
   for(;p.n<MS;){
    if(p.h<0||p.h>=N||!qs.count(p.q))break;
    int bit=(p.t>>p.h)&1,ri=rix[p.q]>=0?rix[p.q]+bit:-1;
    if(ri>=0&&!(known&(1<<ri))){output.push_back(p);blocked=true;break;}
    checks++;Row row=ri>=0?rows[ri]:T[p.q][bit];
    p.t=(p.t&~(1<<p.h))|(row.w<<p.h);p.h+=row.d;p.q=red(row.z);p.n++;
    for(auto g:cases[p.ci].goals)if((p.q==254&&g.q==254)||(p.q==g.q&&p.h==g.h&&p.t==g.t)){met=true;break;}
    if(met)break;
   }
   if(!met&&!blocked)return false;
  }
  return true;
 };

 long long boot_tests=0,boot_hits=0;bool found_boot=false;
 struct BKey{int q,h;uint64_t lo,hi;bool operator==(const BKey&o)const{return q==o.q&&h==o.h&&lo==o.lo&&hi==o.hi;}};
 struct BHash{size_t operator()(const BKey&k)const{return k.lo^(k.hi*0x9e3779b97f4a7c15ULL)^(uint64_t(k.q*1337+k.h)*0xbf58476d1ce4e5b9ULL);}};
 auto rowof=[&](int q,int b)->Row{return rix[q]>=0?rows[rix[q]+b]:T[q][b];};
 auto blank=[&](int initialstate)->bool{
  boot_tests++;vector<unsigned char>tape(65536);set<int>ones;int q=initialstate,h=32768;
  unordered_set<BKey,BHash>seen;
  auto ray=[&](int q,int d)->bool{set<int>visited;while(qs.count(q)){if(!visited.insert(q).second)return true;Row r=rowof(q,0);if(r.d!=d)return false;q=r.z;}return false;};
  for(int n=0;n<3000000;n++){
   if((n&4095)==0&&elapsed()>budget){timeout=true;return false;}
   if(!qs.count(q)||h<2||h>=65534)return false;
   if(q==84&&ones.size()>=11&&*ones.begin()==h-1){
    auto it=ones.upper_bound(h-1);
    if(it!=ones.end()&&*it>=h+64){
     int gap=*it-h-64,c=*it+1;vector<int>v;bool valid=true;
     while(c<=*ones.rbegin()){
      if(c+1>=65536||tape[c]||!tape[c+1]){valid=false;break;}
      int count=0;c++;while(c<65536&&tape[c]){count++;c++;}v.push_back(count-1);
     }
     if(valid&&v.size()>=10&&v[0]==0&&v[2]==0&&v[4]==0&&v[5]==0&&v[7]==0&&v[8]==0){
      boot_hits++;found_boot=true;cout<<"BOOT_HIT start "<<initialstate<<" steps "<<n<<" head "<<h-32768<<" gap "<<gap<<" values";for(int x:v)cout<<" "<<x;cout<<" ones";for(int p:ones)cout<<" "<<p-32768;cout<<"\n";
      cout<<"ROWS";for(int ri=0;ri<NR;ri++)cout<<" q "<<mutableq[ri/2]<<" b "<<ri%2<<" w "<<rows[ri].w<<" d "<<rows[ri].d<<" z "<<rows[ri].z;cout<<"\n"<<flush;return true;
     }
    }
   }
   int bit=tape[h];
   if(!bit&&(ones.empty()||h>*ones.rbegin())&&ray(q,1))return false;
   if(!bit&&(ones.empty()||h<*ones.begin())&&ray(q,-1))return false;
   if(n%32==0&&(ones.empty()||*ones.rbegin()-*ones.begin()<128)){
    int mn=ones.empty()?h:*ones.begin();BKey key{q,h-mn,0,0};
    for(int p:ones){int j=p-mn;if(j<64)key.lo|=1ULL<<j;else key.hi|=1ULL<<(j-64);}
    if(!seen.insert(key).second)return false;
   }
   Row row=rowof(q,bit);
   if(row.w){tape[h]=1;ones.insert(h);}else{tape[h]=0;ones.erase(h);}
   h+=row.d;q=row.z;
  }
  return false;
 };
 auto search=[&](auto&&self,int depth,int known,const vector<Pending>&pending)->void{
  if(timeout||found_boot)return;
  if((++nodes&1023)==0&&elapsed()>budget){timeout=true;return;}
  if(depth==NR||pending.empty()){
   if(!pending.empty())return;
   for(int ri=0;ri<NR;ri++)if(!(known&(1<<ri))){rows[ri]=T[mutableq[ri/2]][ri%2];rows[ri].z=red(rows[ri].z);}
   hits++;
   if(blank(0)||timeout)return;
   if(argc>11&&string(argv[11])=="all_starts")for(int q:qs)if(q!=0){if(blank(q)||timeout)return;}
   if(hits%100==0)cerr<<"NEUTRAL "<<hits<<" boot_tests "<<boot_tests<<" seconds "<<elapsed()<<"\n"<<flush;
   return;
  }
  int bestrow=-1;vector<pair<Row,vector<Pending>>>best;
  for(int ri:order){
   if(known&(1<<ri))continue;
   vector<pair<Row,vector<Pending>>>trial;
   for(auto action:domains[ri]){
    rows[ri]=action;choices++;
    if((choices&4095)==0&&elapsed()>budget){timeout=true;return;}
    vector<Pending>next;
    if(advance(pending,next,known|(1<<ri)))trial.push_back({action,move(next)});
    if(bestrow>=0&&trial.size()>best.size())break;
   }
   if(trial.empty())return;
   if(bestrow<0||trial.size()<best.size()){bestrow=ri;best=move(trial);}
   if(best.size()==1)break;
  }
  for(auto&[action,next]:best){
   rows[bestrow]=action;
   self(self,depth+1,known|(1<<bestrow),next);
   if(timeout||found_boot)return;
  }
 };
 search(search,0,0,initial);
 cerr<<"status "<<(found_boot?"BOOT_HIT":timeout?"INCOMPLETE_TIMEOUT":"COMPLETED")<<" choices "<<choices<<" nodes "<<nodes
     <<" checks "<<checks<<" neutral_solutions "<<hits<<" boot_tests "<<boot_tests<<" boot_hits "<<boot_hits<<" seconds "<<elapsed()<<" old_bound "<<OS<<" new_bound "<<MS<<"\n";
}
