// Finite discovery only: allow clean return PCs in one exact guarded class.
#include <algorithm>
#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
using namespace std;
struct Row { int w=0, d=0, q=-1; };
struct Case {
  bitset<512> tape, used;
  int expected_class, maximum_rank, halt, head;
  array<int,9> regs;
};
array<array<Row,2>,512> table;
vector<array<int,2>> decoder;
vector<int> leaf_class, leaf_rank, states;
vector<Case> cases;
int root;
long long ticks=0, executed=0, recipes=0;

bool matches(const bitset<512>& tape, int h, const Case& c) {
  if(h<1 || h+40>=512 || !tape[h-1]) return false;
  for(int j=0;j<h-1;j++) if(tape[j]) return false;
  int node=root, depth=0;
  while(node>=0) {
    if(depth>40 || h+depth>=512) return false;
    node=decoder[node][tape[h+depth]];
    depth++;
  }
  int leaf=-node-1;
  if(leaf_class[leaf]!=c.expected_class || leaf_rank[leaf]>c.maximum_rank) return false;
  // A clean stored path must have no nonzero unused suffix past the leaf.
  int header=h+40;
  while(header<512 && !tape[header]) header++;
  if(header>=512) return false;
  for(int j=h+depth;j<header;j++) if(tape[j]) return false;
  int at=header+1;
  for(int value:c.regs) {
    if(at+value+2>=512 || tape[at]) return false;
    for(int k=1;k<=value+1;k++) if(!tape[at+k]) return false;
    at+=value+2;
  }
  int last=511;
  while(last>=at && !tape[last]) last--;
  if(last<=at || tape[at]) return false;
  for(int j=at;j<last;j++) if(!tape[j]&&!tape[j+1]) return false;
  return true;
}

bool test_case(int id, int removed, int target) {
  const auto& c=cases[id]; auto tape=c.tape; int q=96,h=128,visits=0;
  executed++;
  for(int t=0;t<4000;t++) {
    if(h<0||h>=512||q<0||q>=512) return false;
    Row r=table[q][tape[h]];
    if(r.q<0) return false;
    tape[h]=r.w; h+=r.d; q=r.q==removed?target:r.q; ticks++;
    if(q==254) return c.halt==254;
    if(q==96) {
      if(c.halt==96 && matches(tape,h,c)) return true;
      if(++visits>15) return false;
    }
  }
  return false;
}

int main(int argc,char**argv) {
  if(argc!=5) return 2;
  ifstream f(argv[1]); string line; getline(f,line);
  int q,b,w,t; char direction;
  while(f>>q>>b>>w>>direction>>t) {
    table[q][b]={w,direction=='R'?1:-1,t};
    if(b==0) states.push_back(q);
  }
  ifstream d(argv[2]); int n,k; d>>n>>root>>k;
  decoder.resize(n);leaf_class.resize(k);leaf_rank.resize(k);
  for(auto& row:decoder)d>>row[0]>>row[1];
  for(int j=0;j<k;j++)d>>leaf_class[j]>>leaf_rank[j];
  ifstream in(argv[3]);
  Case c;
  while(in>>c.expected_class>>c.maximum_rank>>n) {
    c.tape.reset();c.used.reset();
    for(int j=0;j<n;j++){in>>k;c.tape[k+128]=1;}
    string pc;in>>c.halt>>c.head>>pc;
    for(auto& r:c.regs)in>>r;
    in>>n;for(int j=0;j<n;j++)in>>k;
    in>>n;for(int j=0;j<n;j++){in>>k;c.used[k]=1;}
    cases.push_back(c);
  }
  for(int j=0;j<(int)cases.size();j++)if(!test_case(j,-1,-1)) {
    cerr<<"BASELINE FAIL "<<j<<endl;return 3;
  }
  cerr<<"BASELINE PASS "<<cases.size()<<endl;
  const string mode=argv[4];
  vector<int> order(cases.size());iota(order.begin(),order.end(),0);
  mt19937 random(20261018);shuffle(order.begin(),order.end(),random);
  int survivors=0;
  for(int removed:states) {
    if(removed==96)continue;
    vector<int> touching;
    for(int i:order)if(cases[i].used[2*removed]||cases[i].used[2*removed+1])touching.push_back(i);
    for(int target:states) {
      if(target==removed)continue;
      if(mode=="uniform" || mode=="mixed") {
        for(int keep=-1;keep<(mode=="mixed"?2:0);keep++) {
          auto before=keep<0?Row{}:table[target][keep];
          if(keep>=0)table[target][keep]=table[removed][keep];
          bool pass=true;recipes++;
          if(keep<0) {
            for(int id:touching)if(!test_case(id,removed,target)){pass=false;break;}
          } else {
            for(int id:order)if(cases[id].used[2*removed]||cases[id].used[2*removed+1]||cases[id].used[2*target+keep])
              if(!test_case(id,removed,target)){pass=false;break;}
          }
          if(pass) {
            cout<<"SURVIVOR removed="<<removed<<" target="<<target<<" copy="<<keep<<endl;survivors++;
          }
          if(keep>=0)table[target][keep]=before;
        }
      }
    }
    cerr<<"STATE "<<removed<<" recipes="<<recipes<<" tests="<<executed<<" ticks="<<ticks<<endl;
  }
  cout<<"DONE recipes="<<recipes<<" tests="<<executed<<" ticks="<<ticks<<" survivors="<<survivors<<endl;
}
