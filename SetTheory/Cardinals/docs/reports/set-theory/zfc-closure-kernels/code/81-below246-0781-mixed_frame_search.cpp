#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
using namespace std;
struct Row {int w,d,q;};
array<array<Row,2>,256> T, original;
struct Case {bitset<512> a,z,used; int q,h; string pc; array<int,9> regs;};
vector<Case> tests;
bool matches(const bitset<512>&tape,const Case &ex,int h){
 if(h<1||h+40>=512||!tape[h-1])return false;
 for(int i=0;i<h-1;i++)if(tape[i])return false;
 for(int i=0;i<(int)ex.pc.size();i++)if(h+i>=512||tape[h+i]!=(ex.pc[i]=='1'))return false;
 int header=h+ex.pc.size();while(header<512&&!tape[header])header++;
 if(header==512||header-h<40)return false;
 int at=header+1;
 for(int r:ex.regs){
  if(at>=512||tape[at])return false;
  for(int j=1;j<=r+1;j++)if(at+j>=512||!tape[at+j])return false;
  at+=r+2;
 }
 int last=511;while(last>=at&&!tape[last])last--;
 if(last<=at||tape[at])return false;
 for(int i=at;i<last;i++)if(!tape[i]&&!tape[i+1])return false;
 return true;
}
int main(int argc,char**argv) {
 if(argc!=3) return 2;
 ifstream tf(argv[1]); string s; getline(tf,s); int q,b,w,t; char d;
 vector<int> states;
 while(tf>>q>>b>>w>>d>>t) {T[q][b]={w,d=='R'?1:-1,t}; if(b==0) states.push_back(q);}
 original=T;
 ifstream f(argv[2]); int n,k;
 while(f>>n) {Case c; for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;} f>>c.q>>c.h>>c.pc;c.h+=128; if(c.pc=="-")c.pc=""; for(int &r:c.regs)f>>r; f>>n;
  for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;} f>>n;for(int i=0;i<n;i++){f>>k;c.used[k]=1;} tests.push_back(c);}
 vector<int> order(tests.size());for(int i=0;i<(int)order.size();i++)order[i]=i;
 shuffle(order.begin(),order.end(),mt19937(246245));
 long long cases=0,steps=0,recipes=0;int survivors=0;
 for(int a:states) {
  if(a==96)continue;
  for(int c:states)if(a!=c)for(int borrow=0;borrow<2;borrow++) {
   Row from=original[a][borrow],to=original[c][borrow];
   if(from.w==to.w&&from.d==to.d&&from.q==to.q)continue;
   T=original;T[c][borrow]=from;
   for(int st:states)for(int bit=0;bit<2;bit++)if(T[st][bit].q==a)T[st][bit].q=c;
   ++recipes;bool ok=true;
   for(int ci:order) {
    const Case& ex=tests[ci];
    if(!ex.used[2*a]&&!ex.used[2*a+1]&&!ex.used[2*c+borrow])continue;
    auto tape=ex.a;int state=96,h=128,visits=0;bool pass=false;
    for(int tick=0;tick<6000;tick++) {
     if(h<0||h>=512)break;
     auto row=T[state][tape[h]];tape[h]=row.w;h+=row.d;state=row.q;++steps;
     if(state==254){pass=ex.q==254;break;}
     if(state==96){if(ex.q==96&&matches(tape,ex,h)){pass=true;break;}if(++visits>24)break;}
    }
    ++cases;if(!pass){ok=false;break;}
   }
   if(ok){cout<<"SURVIVOR removed="<<a<<" retained="<<c<<" borrowed_read="<<borrow<<endl;++survivors;}
  }
 }
 cout<<"DONE recipes="<<recipes<<" survivors="<<survivors<<" cases="<<cases<<" transitions="<<steps<<" fuel=6000 tape_cells=512 max_intermediate_dispatches=24"<<endl;
}
