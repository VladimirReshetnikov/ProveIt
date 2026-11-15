// Trace-driven enumeration of static edits from a finite proposal pool.
// Search evidence only: every hit still needs source and runtime proofs.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>
#include <unordered_map>
using namespace std;
struct Action { int w=0,d=0,n=-1; };
struct Edit { int id,q,b,w,d,n; };
struct Node { int child[2]={-1,-1},site=-1; };
constexpr int Q=3000,RAD=20000,OFF=RAD+1;
using Table=array<array<Action,2>,Q>;
Table base;
array<bool,Q> exists{};
array<vector<Edit>,2*Q> alternatives;
vector<int> states;
vector<Node> trie(1);
long long entered=0,ticks=0,halts=0,rays=0,bounded=0,cycles=0,hits=0,cap;
int fuel,depth_limit;
bool stopped=false;
ofstream hitstream;
struct Run {
 Table rows;
 array<bool,2*Q> decided{};
 vector<unsigned char> tape=vector<unsigned char>(2*RAD+3);
 vector<int> edits;
 int q,h=0,left=1,right=-1,ones=0,time=0,start;
};
bool ray(const Run &s) {
 if(s.tape[s.h+OFF] || (s.ones && s.h>=s.left && s.h<=s.right)) return false;
 array<bool,Q> seen{};
 int q=s.q,d=0;
 while(q>=0 && q<Q && exists[q] && !seen[q]) {
  if((int)s.edits.size()<depth_limit && !s.decided[2*q] && !alternatives[2*q].empty()) return false;
  seen[q]=true;auto a=s.rows[q][0];
  if(d && d!=a.d)return false;
  d=a.d;q=a.n;
 }
 return q>=0 && q<Q && seen[q] && (!s.ones || (d==1 && s.h>s.right) || (d==-1 && s.h<s.left));
}
bool frame(const Run &s) {
 if(s.q!=84 || s.ones<12 || s.left!=s.h-1 || s.h+38>=RAD)return false;
 int a=0,len=0;
 while(trie[a].site<0 && len<38){int b=s.tape[s.h+len+OFF];a=trie[a].child[b];++len;if(a<0)break;}
 if(a<0 || trie[a].site<0)return false;
 int sep=s.h+len;while(sep<=s.right && !s.tape[sep+OFF])++sep;
 if(sep>s.right)return false;
 vector<int>values;int p=sep;
 while(p<s.right){
  if(s.tape[p+1+OFF] || !s.tape[p+2+OFF])return false;
  p+=2;int v=0;while(p<s.right && s.tape[p+1+OFF]){++p;++v;}values.push_back(v);
 }
 if(values.size()<10)return false;
 ++hits;hitstream<<"{\"edits\":[";
 for(size_t i=0;i<s.edits.size();++i){if(i)hitstream<<',';hitstream<<s.edits[i];}
 hitstream<<"],\"start\":"<<s.start<<",\"steps\":"<<s.time<<",\"site\":"<<trie[a].site<<",\"head\":"<<s.h<<",\"span\":"<<sep-s.h<<",\"values\":[";
 for(size_t i=0;i<values.size();++i){if(i)hitstream<<',';hitstream<<values[i];}
 hitstream<<"],\"ones\":[";bool first=true;
 for(int p=s.left;p<=s.right;++p)if(s.tape[p+OFF]){if(!first)hitstream<<',';first=false;hitstream<<p;}
 hitstream<<"]}\n";hitstream.flush();return true;
}
void explore(Run s) {
 if(stopped)return;
 if(entered>=cap){stopped=true;return;}
 ++entered;
 if(entered%1000==0)cerr<<"branches "<<entered<<" ticks "<<ticks<<" hits "<<hits<<'\n';
 unordered_map<long long,long long> last;long long changes=0;
 for(;;) {
  if(s.q<0 || s.q>=Q || !exists[s.q]){++halts;return;}
  if(s.time>=fuel || abs(s.h)>=RAD){++bounded;return;}
  if(frame(s))return;
  int b=s.tape[s.h+OFF],key=2*s.q+b;
  if((int)s.edits.size()<depth_limit && !s.decided[key] && !alternatives[key].empty()) {
   s.decided[key]=true;
   for(const Edit&e:alternatives[key]) {
    Run child=s;child.rows[e.q][e.b]={e.w,e.d,e.n};child.edits.push_back(e.id);
    explore(move(child));if(stopped)return;
   }
  }
  if(ray(s)){++rays;return;}
  long long key2=(long long)s.q*(2*RAD+3)+s.h+OFF;
  auto it=last.find(key2);if(it!=last.end()&&it->second==changes){++cycles;return;}last[key2]=changes;
  Action a=s.rows[s.q][b];if(a.w!=b)++changes;
  if(a.w && !b){s.tape[s.h+OFF]=1;++s.ones;if(s.ones==1)s.left=s.right=s.h;else{s.left=min(s.left,s.h);s.right=max(s.right,s.h);}}
  else if(!a.w && b){s.tape[s.h+OFF]=0;--s.ones;if(!s.ones){s.left=1;s.right=-1;}else{if(s.h==s.left)while(!s.tape[++s.left+OFF]){};if(s.h==s.right)while(!s.tape[--s.right+OFF]){}}}
  s.h+=a.d;s.q=a.n;++s.time;++ticks;
 }
}
int main(int argc,char**argv) {
 if(argc!=8){cerr<<"table edits paths max_edits fuel max_branches hits_file\n";return 2;}
 depth_limit=stoi(argv[4]);fuel=stoi(argv[5]);cap=stoll(argv[6]);
 int q,b,w,n;char d;ifstream in(argv[1]);while(in>>q>>b>>w>>d>>n){if(!exists[q])states.push_back(q);exists[q]=true;base[q][b]={w,d=='R'?1:-1,n};}
 if(states.size()!=193)return 3;
 Edit e;ifstream ed(argv[2]);while(ed>>e.id>>e.q>>e.b>>e.w>>e.d>>e.n){if(!exists[e.q] || (e.n!=254&&!exists[e.n]))return 4;alternatives[2*e.q+e.b].push_back(e);}
 string path;int site,mask;ifstream ps(argv[3]);while(ps>>site>>path>>mask){int a=0;for(char c:path){int b=c-'0';if(trie[a].child[b]<0){int z=trie.size();trie[a].child[b]=z;trie.emplace_back();}a=trie[a].child[b];}trie[a].site=site;}
 hitstream.open(argv[7]);auto begin=chrono::steady_clock::now();int completed_starts=0;
 stable_sort(states.begin(),states.end(),[](int a,int b){return a==74 && b!=74;});
 for(int q:states){Run s;s.rows=base;s.start=s.q=q;explore(move(s));if(stopped)break;++completed_starts;}
 cout<<"{\"method\":\"trace-driven static edit enumeration\",\"max_edits\":"<<depth_limit<<",\"fuel\":"<<fuel<<",\"branch_cap\":"<<cap<<",\"stopped_at_cap\":"<<(stopped?"true":"false")<<",\"completed_initial_controls\":"<<completed_starts<<",\"branches\":"<<entered<<",\"transitions\":"<<ticks<<",\"halts\":"<<halts<<",\"outward_rays\":"<<rays<<",\"bounded\":"<<bounded<<",\"unchanged_tape_cycles\":"<<cycles<<",\"frame_hits\":"<<hits<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<"}\n";
}
