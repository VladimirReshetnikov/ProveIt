// Bounded joint-selector discovery. Positive results require independent replay.
// C++17, standard library only. No negative result establishes a state bound.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <deque>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
struct A {int w=0,d=0,z=-1;};
struct C {int q,h,m;};
static array<array<A,2>,512> O,N;
static int rad=7,mask=(1<<15)-1,phi[512];
static uint64_t key(C c){return ((uint64_t(c.q)*64+uint64_t(c.h+24))<<15)|c.m;}
static C step(const array<array<A,2>,512>&T,C c){
 int b=(c.m>>(c.h+rad))&1;A a=T[c.q][b];
 return {a.z,c.h+a.d,(c.m&~(1<<(c.h+rad)))|(a.w<<(c.h+rad))};
}
struct Case {int q,b;vector<int> words;};
struct Path {vector<uint64_t> goals;bool halt=false;};
int main(int argc,char**argv){
 if(argc<5){cerr<<"usage: search BASE.tm family(124|52) OUT_PREFIX first_directions(0|1)\n";return 2;}
 ifstream in(argv[1]);string line;vector<int> Q;array<bool,512> present{};int start=0;
 while(getline(in,line)){
  if(line.rfind("#! start ",0)==0){start=stoi(line.substr(9));continue;}
  if(line.empty()||line[0]=='#')continue;
  stringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;
  if(!s||q<0||q>=512||z<0||z>=512)return 3;
  O[q][b]={w,d=='R'?1:-1,z};present[q]=true;
 }
 for(int q=0;q<512;q++)if(present[q])Q.push_back(q);
 if(Q.size()!=215||present[254])return 4;
 for(int q=0;q<512;q++)phi[q]=q;
 int family=stoi(argv[2]);int a=family==124?124:52,da=family==124?127:176;
 int b=160,db=190;
 if(argc==9){a=stoi(argv[5]);da=stoi(argv[6]);b=stoi(argv[7]);db=stoi(argv[8]);}
 vector<int> altered={a,da,b,db};sort(altered.begin(),altered.end());
 if(unique(altered.begin(),altered.end())!=altered.end())return 5;
 for(int q:altered)if(!present[q]||q==start)return 6;
 phi[da]=a;phi[db]=b;
 vector<vector<uint8_t>> dom(512,vector<uint8_t>(mask+1,0));
 vector<pair<int,int>> todo;todo.reserve(3000000);
 for(int m=0;m<=mask;m++){dom[start][m]=1;todo.emplace_back(start,m);}
 for(size_t pos=0;pos<todo.size();pos++){
  auto[q,m]=todo[pos];if(q==254)continue;
  A act=O[q][(m>>rad)&1];int x=(m&~(1<<rad))|(act.w<<rad),n0,n1;
  if(act.d==1){n0=x>>1;n1=n0|(1<<(2*rad));}
  else {n0=(x<<1)&mask;n1=n0|1;}
  for(int n:{n0,n1})if(!dom[act.z][n]){dom[act.z][n]=1;todo.emplace_back(act.z,n);}
 }
 vector<Case> cases;
 for(int q:altered)for(int bit=0;bit<2;bit++){
  Case k{q,bit,{}};for(int m=0;m<=mask;m++)if(dom[q][m]&&((m>>rad)&1)==bit)k.words.push_back(m);
  if(k.words.size()>2)rotate(k.words.begin()+1,k.words.end()-1,k.words.end());
  cases.push_back(move(k));
 }
 unordered_map<uint64_t,Path> cache;
 int activeHelper=-1;
 auto pass=[&]()->int{
  for(const Case& cs:cases){
   A x=O[cs.q][cs.b],y=N[phi[cs.q]][cs.b];
   if(y.w==x.w&&y.d==x.d&&y.z==phi[x.z])continue;
   for(int m:cs.words){
    uint64_t id=uint64_t(cs.q)*(mask+1)+m;auto it=cache.find(id);
    if(it==cache.end()){
     Path p;C c{cs.q,0,m};
     for(int j=0;j<97;j++){
      if(c.q==254||c.h < -rad||c.h>rad)break;
      c=step(O,c);p.halt|=c.q==254;
      C mapped=c;mapped.q=phi[c.q];p.goals.push_back(key(mapped));
     }
     sort(p.goals.begin(),p.goals.end());p.goals.erase(unique(p.goals.begin(),p.goals.end()),p.goals.end());
     it=cache.emplace(id,move(p)).first;
    }
    const Path& p=it->second;C c{phi[cs.q],0,m};array<uint64_t,97> seen{};int ns=0;bool ok=false,usedInner=false;
    for(int j=0;j<97;j++){
     if(c.q==254||c.h < -rad||c.h>rad)break;
     uint64_t kk=key(c);if(find(seen.begin(),seen.begin()+ns,kk)!=seen.begin()+ns)break;
     seen[ns++]=kk;
     usedInner|=c.q==activeHelper&&((c.m>>(c.h+rad))&1)==1;
     c=step(N,c);
     if(c.q==254){ok=p.halt;break;}
     if(binary_search(p.goals.begin(),p.goals.end(),key(c))){ok=true;break;}
    }
    if(!ok)return usedInner?0:-1;
   }
  }
  return 1;
 };
 bool fullDirections=stoi(argv[4]);string prefix=argv[3];uint64_t count=0,hits=0,evaluated=0,uniformlyPruned=0;
 auto begun=chrono::steady_clock::now();
 for(int helper:{da,db}){
  activeHelper=helper;
  int dropped=helper==da?db:da;vector<int> targets;for(int q:Q)if(q!=dropped)targets.push_back(q);
  for(int q:Q)for(int bit=0;bit<2;bit++){A x=O[q][bit];N[q][bit]={x.w,x.d,phi[x.z]};}
  for(int wa=0;wa<2;wa++)for(int wb=0;wb<2;wb++)for(int ea:{-1,1})for(int eb:{-1,1}){
   if(!fullDirections&&(ea!= -1||eb!= -1))continue;
   N[a][0]={wa,ea,helper};N[b][1]={wb,eb,helper};
   for(int h0w=0;h0w<2;h0w++)for(int h0d:{-1,1})for(int p0:targets){
    N[helper][0]={h0w,h0d,p0};
    {int innerIndex=0;
    for(int h1w=0;h1w<2;h1w++)for(int h1d:{-1,1})for(int p1:targets){
     N[helper][1]={h1w,h1d,p1};count++;innerIndex++;evaluated++;
     int result=pass();
     if(result==-1){uint64_t skip=4*targets.size()-innerIndex;count+=skip;uniformlyPruned+=skip;goto nextOuter;}
     if(result==0)continue;
     hits++;
     string name=prefix+"-hit"+to_string(hits)+".tm";ofstream o(name);o<<"#! start "<<start<<'\n';
     for(int q:targets)for(int bit=0;bit<2;bit++){A x=N[q][bit];o<<q<<' '<<bit<<' '<<x.w<<' '<<(x.d==1?'R':'L')<<' '<<x.z<<'\n';}
     cout<<"SURVIVOR "<<name<<" helper "<<helper<<" map "<<da<<":"<<a<<","<<db<<":"<<b<<endl;
    }
    nextOuter:;}
   }
   double seconds=chrono::duration<double>(chrono::steady_clock::now()-begun).count();
   cout<<"progress "<<helper<<' '<<wa<<wb<<' '<<ea<<' '<<eb<<' '<<count<<' '<<seconds<<endl;
  }
 }
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-begun).count();
 ofstream receipt(prefix+".json");receipt<<"{\n  \"family\": "<<family<<",\n  \"role_pairs\": [["<<a<<","<<da<<"],["<<b<<","<<db<<"]],\n  \"candidates\": "<<count<<",\n  \"evaluated\": "<<evaluated<<",\n  \"uniformly_pruned\": "<<uniformlyPruned<<",\n  \"survivors\": "<<hits<<",\n  \"radius\": 7,\n  \"fuel\": 97,\n  \"all_first_directions\": "<<(fullDirections?"true":"false")<<",\n  \"seconds\": "<<seconds<<",\n  \"domain_contexts_including_halt\": "<<todo.size()<<"\n}\n";
 cout<<"DONE "<<count<<' '<<hits<<' '<<seconds<<endl;
}
