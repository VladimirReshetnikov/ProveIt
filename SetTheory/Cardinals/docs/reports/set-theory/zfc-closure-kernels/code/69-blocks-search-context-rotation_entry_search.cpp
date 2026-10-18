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
struct Row{int w,d,t;};Row table[512][2];vector<int> states;
struct Case{array<unsigned char,512> tape,target;int head,targethead;bool halt;bitset<1024> used;string label;};
string addone(string s){int i=s.size()-1;while(i>=0&&s[i]=='1')s[i--]='0';if(i<0)return "!";s[i]='1';return s;}
string strip(string s,char b,int k){int i=s.size();while(i&&k){if(s[--i]==b)--k;}return s.substr(0,i);}
array<unsigned char,512> paint(string s,int span,vector<int> regs,int h){array<unsigned char,512> t{};t[h-1]=t[h+span]=1;for(int i=0;i<(int)s.size();i++)t[h+i]=s[i]=='1';int p=h+span+1;for(int v:regs){for(int j=1;j<=v+1;j++)t[p+j]=1;p+=v+2;}return t;}
// 0 is a witnessed bounded failure, 1 is the required endpoint, 2 hits
// the not-yet-selected receiving row. Bounds reject, never certify.
bool simulate(const Case& c,int removed,int sq,int sb,Row replacement){
 auto tape=c.tape;int q=96,h=c.head,visits=0;
 for(int n=0;n<2500;n++){
  if(q==removed)return false;
  auto row=q==sq&&tape[h]==sb?replacement:table[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.t;
  if(q==254)return c.halt;
  if(h<8||h>=504)return false;
  if(q==96){if(!c.halt&&h==c.targethead&&tape==c.target)return true;if(++visits>15)return false;}
 }
 return false;
}
int main(int argc,char**argv){
 ifstream tm(argv[1]);string line;
 set<int> qs;while(getline(tm,line))if(line.size()&&line[0]!='#'){stringstream s(line);int q,b,w,t;char d;s>>q>>b>>w>>d>>t;table[q][b]={w,d=='R'?1:-1,t};qs.insert(q);}states={qs.begin(),qs.end()};
 set<int> macros={2,4,6,20,48,63,73,75,83,95,109,112,131,255,60,44,31,56,38,40,28,64,69};
 auto immutable=[&](int q,int b){if(!macros.count(q))return false;return !((q==6&&b==0)||(q==20&&b==0)||(q==48&&b==0)||(q==69&&b==1));};
 ifstream sites(argv[2]);string p,op;int r;vector<Case> cases;
 int phy[9]={6,2,0,4,3,7,8,5,1};long long ticks=0;
 while(sites>>p>>op>>r)for(int seed:{0,1,4})for(int branch=0;branch<(op=="CD"?2:1);branch++){
  int h=128,span=40+seed;vector<int> regs;for(int i=0;i<11;i++){int v=i<9?(i*3+seed)%7:seed%3;if(op=="CD"&&i==phy[r])v=branch?seed+1:0;regs.push_back(v);}
  auto t=paint(p,span,regs,h);string nxt;int eh=h,es=span;
  if(op=="CI"){regs[phy[r]]++;regs.push_back(1);nxt=addone(p);}
  else if(op=="CD"){if(branch){regs[phy[r]]--;es++;nxt=addone(p);}else nxt=addone(strip(p,'0',1));}
  else if(op=="CB")nxt=addone(strip(p,'0',r));else if(op=="CC")nxt=strip(p,'1',r);
  if(nxt=="!"){nxt="";eh--;es++;}
  Case c{t,paint(nxt,es,regs,eh),h,eh,op=="CH",{},p+" "+op+" "+to_string(r)+" "+to_string(seed)+" "+to_string(branch)};
  int q=96;bool done=false;for(int k=0;k<100000;k++){
   c.used[q*2+t[h]]=1;auto a=table[q][t[h]];t[h]=a.w;h+=a.d;q=a.t;ticks++;
   if(q==254){done=c.halt;break;}if(q==96&&!c.halt&&h==eh&&t==c.target){done=true;break;}
   if(h<1||h>=511)break;
  }
  if(!done){cerr<<"Baseline failure "<<c.label<<"\n";return 1;}cases.push_back(move(c));
 }
 cerr<<"cases "<<cases.size()<<" baseline_ticks "<<ticks<<"\n";
 auto start=chrono::steady_clock::now();long long trials=0,survivors=0;
 for(int u:states)if(u!=96&&!macros.count(u)){
  vector<pair<int,int>> incoming;
  for(int q:states)if(q!=u)for(int b:{0,1})if(table[q][b].t==u)incoming.push_back({q,b});
  if(incoming.size()!=1)continue;
  auto [sq,sb]=incoming[0];if(immutable(sq,sb))continue;
  vector<const Case*> affected;for(auto& c:cases)if(c.used[sq*2+sb])affected.push_back(&c);
  stable_sort(affected.begin(),affected.end(),[](auto a,auto b){return a->label.size()>b->label.size();});
  for(int v:states)if(v!=u)for(int w:{0,1})for(int d:{-1,1}){
   trials++;bool ok=true;Row a{w,d,v};
   for(int i=0;i<(int)affected.size();i++)if(!simulate(*affected[i],u,sq,sb,a)){ok=false;swap(affected[0],affected[i]);break;}
   if(ok){survivors++;cout<<u<<" "<<sq<<" "<<sb<<" "<<w<<" "<<d<<" "<<v<<"\n"<<flush;}
  }
 }
 cerr<<"COMPLETE trials "<<trials<<" survivors "<<survivors<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
