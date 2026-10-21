// Finite candidate discovery only. No bounded failure proves inequivalence.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
constexpr int OFFSET=1024, WIDTH=8192, MAXQ=512;
struct Action{int w=-1,d=0,z=-1;bool operator==(const Action&a)const{return w==a.w&&d==a.d&&z==a.z;}};
using Table=array<Action,MAXQ*2>;
struct Tape{
 bitset<WIDTH> bits;int lo=WIDTH-OFFSET,hi=-OFFSET-1;
 bool read(int h)const{return bits[h+OFFSET];}
 void write(int h,int v){bits[h+OFFSET]=v;if(v){lo=min(lo,h);hi=max(hi,h);}else if(lo<=hi){if(h==lo){while(lo<=hi&&!read(lo))lo++;}if(h==hi){while(hi>=lo&&!read(hi))hi--;}}}
 bool operator==(const Tape&t)const{return bits==t.bits;}
};
struct Case{int ordinal,positive,trial,targetq,targeth;Tape input,target;vector<int>used;long steps=0;};
struct Result{int status,q,h;long steps;Tape tape;vector<int>used;};
Table load_table(string file,vector<int>&states){
 Table t;ifstream f(file);string l;
 while(getline(f,l))if(l.size()&&l[0]!='#'){
  istringstream s(l);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;
  if(!s||q<0||q>=MAXQ||b<0||b>1||w<0||w>1||(d!='L'&&d!='R'))throw runtime_error("Bad table");
  t[2*q+b]={w,d=='R'?1:-1,z};if(!b)states.push_back(q);
 }
 return t;
}
vector<Case> load_cases(string file){
 ifstream f(file);int n;f>>n;vector<Case>cases;
 for(int k=0;k<n;k++){
  Case c;int count,x;f>>c.ordinal>>c.positive>>c.trial>>count;
  for(int j=0;j<count;j++){f>>x;c.input.write(x,1);}
  f>>c.targetq>>c.targeth>>count;
  for(int j=0;j<count;j++){f>>x;c.target.write(x,1);}
  if(!f)throw runtime_error("Bad case");cases.push_back(c);
 }
 return cases;
}
bool clean(int h,const Tape&t){
 if(t.lo!=h-1)return false;
 int header=h+52;while(header<=t.hi&&!t.read(header))header++;
 if(header>t.hi||header<h+64)return false;
 int p=header+1,count=0;
 while(p<=t.hi){if(t.read(p)||!t.read(p+1))return false;p++;while(p<=t.hi&&t.read(p))p++;count++;}
 return count>=10;
}
Result simulate(const Table&t,const Case&c,int cap=20000,bool record=false){
 Tape tape=c.input;int q=84,h=0;bitset<MAXQ*2> seen;
 for(int k=0;k<=cap;k++){
  if(q==254)return {c.targetq==254?0:1,q,h,k,tape,{}};
  if(k&&q==84){
   if(c.targetq==84&&h==c.targeth&&tape==c.target){vector<int>u;if(record)for(int i=0;i<MAXQ*2;i++)if(seen[i])u.push_back(i);return {0,q,h,k,tape,u};}
   if(clean(h,tape))return {1,q,h,k,tape,{}};
  }
  if(k==cap)return {2,q,h,k,tape,{}};
  if(h<-OFFSET+2||h>=WIDTH-OFFSET-2)return {3,q,h,k,tape,{}};
  int b=tape.read(h),key=q*2+b;Action a=t[key];if(a.w<0)return {4,q,h,k,tape,{}};
  if(record)seen[key]=true;
  if(!b&&a.z==q&&((a.d==1&&h>=tape.hi)||(a.d==-1&&h<=tape.lo)))return {5,q,h,k,tape,{}};
  tape.write(h,a.w);h+=a.d;q=a.z;
 }
 throw runtime_error("unreachable");
}
vector<long> parse_root(int h,const Tape&t){
 if(t.lo!=h-1)return{};
 int header=h;while(header<=t.hi&&!t.read(header))header++;
 if(header<h+64||header>t.hi)return{};
 int p=header+1;vector<long>vals;
 while(p<=t.hi){if(t.read(p)||!t.read(p+1))return{};p++;int n=0;while(p<=t.hi&&t.read(p)){p++;n++;}vals.push_back(n-1);}
 if(vals.size()<10)return{};
 int phy[]={6,2,0,4,3,7,8,5,1};vector<long>result={header-h-64};for(int x:phy)result.push_back(vals[x]);result.insert(result.end(),vals.begin()+9,vals.end());return result;
}
Result bootstrap(const Table&t,int start,int cap=1000000,bool record=false){
 Tape tape;int q=start,h=0;bitset<MAXQ*2> seen;
 for(int k=0;k<=cap;k++){
  if(q==254)return {1,q,h,k,tape,{}};
  if(q==84&&!parse_root(h,tape).empty())return {0,q,h,k,tape,{}};
  if(k==cap)return {2,q,h,k,tape,{}};
  if(h<-OFFSET+2||h>=WIDTH-OFFSET-2)return {3,q,h,k,tape,{}};
  int b=tape.read(h),key=2*q+b;Action a=t[key];if(a.w<0)return {4,q,h,k,tape,{}};
  if(record)seen[key]=true;
  if(!b&&a.z==q&&((a.d==1&&h>=tape.hi)||(a.d==-1&&h<=tape.lo))){vector<int>u;if(record)for(int i=0;i<MAXQ*2;i++)if(seen[i])u.push_back(i);return {5,q,h,k,tape,u};}
  tape.write(h,a.w);h+=a.d;q=a.z;
 }
 throw runtime_error("unreachable");
}
void dump_array(const vector<long>&a){cout<<'[';for(size_t i=0;i<a.size();i++){if(i)cout<<',';cout<<a[i];}cout<<']';}
void dump_support(const Tape&t){cout<<'[';bool first=true;for(int i=t.lo;i<=t.hi;i++)if(t.read(i)){if(!first)cout<<',';cout<<i;first=false;}cout<<']';}
int main(int argc,char**argv){
 if(argc<4){cerr<<"table cases output_prefix [allstarts=0]\n";return 2;}
 vector<int>states;Table base=load_table(argv[1],states);auto cases=load_cases(argv[2]);string outprefix=argv[3];bool allstarts=argc>4&&stoi(argv[4]);
 auto began=chrono::steady_clock::now();vector<vector<int>>using_row(MAXQ*2);long baseline_steps=0;int maximum_steps=0;
 for(int i=0;i<(int)cases.size();i++){
  Result r=simulate(base,cases[i],20000,true);
  if(r.status){cerr<<"BASELINE_FAIL "<<i<<' '<<r.status<<' '<<r.steps<<'\n';return 3;}
  cases[i].used=r.used;cases[i].steps=r.steps;baseline_steps+=r.steps;maximum_steps=max(maximum_steps,(int)r.steps);
  for(int key:r.used)using_row[key].push_back(i);
 }
 cerr<<"Baseline passed "<<cases.size()<<" finite cases, steps "<<baseline_steps<<" max "<<maximum_steps<<'\n';
 Result boot=bootstrap(base,0,1000000,true);set<int>keys(boot.used.begin(),boot.used.end());
 if(allstarts){for(int start:states){auto r=bootstrap(base,start,1000000,true);keys.insert(r.used.begin(),r.used.end());}}
 cerr<<"Bootstrap status "<<boot.status<<" steps "<<boot.steps<<" patch rows "<<keys.size()<<'\n';
 vector<Action>actions;for(int w:{0,1})for(int d:{-1,1}){for(int z:states)actions.push_back({w,d,z});actions.push_back({w,d,254});}
 ofstream passfile(outprefix+"-finite-survivors.txt"),summary(outprefix+"-summary.txt");long tested=0,finite_pass=0,boot_success=0,total_sim_steps=0;array<long,6>rejects={};
 for(int key:keys){int row_pass=0;
  for(Action a:actions)if(!(a==base[key])){
   tested++;Table t=base;t[key]=a;bool valid=true;
   for(int j:using_row[key]){auto r=simulate(t,cases[j]);total_sim_steps+=r.steps;if(r.status){valid=false;rejects[r.status]++;break;}}
   if(!valid)continue;
   finite_pass++;row_pass++;passfile<<key/2<<' '<<key%2<<' '<<a.w<<' '<<a.d<<' '<<a.z<<'\n';passfile.flush();
   vector<int>starts={0};if(allstarts)starts=states;
   for(int start:starts){auto r=bootstrap(t,start);total_sim_steps+=r.steps;if(r.status==0){
    boot_success++;cout<<"{\"row\":["<<key/2<<','<<key%2<<"],\"action\":["<<a.w<<','<<a.d<<','<<a.z<<"],\"start\":"<<start<<",\"steps\":"<<r.steps<<",\"head\":"<<r.h<<",\"gap_registers_spares\":";dump_array(parse_root(r.h,r.tape));cout<<",\"support\":";dump_support(r.tape);cout<<"}\n"<<flush;
   }}
  }
  cerr<<"ROW "<<key/2<<'/'<<key%2<<" survivors "<<row_pass<<" total "<<finite_pass<<" boot "<<boot_success<<" elapsed "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
 }
 summary<<"tests "<<tested<<" finite_pass "<<finite_pass<<" boot_success "<<boot_success<<" simulated_steps "<<total_sim_steps<<" baseline_steps "<<baseline_steps<<" maximum_baseline "<<maximum_steps<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
 for(int i=0;i<6;i++)summary<<"rejected_status "<<i<<' '<<rejects[i]<<'\n';
 return 0;
}
