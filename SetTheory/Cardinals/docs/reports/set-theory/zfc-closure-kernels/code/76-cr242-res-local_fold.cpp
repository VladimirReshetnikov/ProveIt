#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Row{int w,d,q; bool operator==(const Row&o)const{return tie(w,d,q)==tie(o.w,o.d,o.q);}};
array<Row,512> T;
vector<int> states;
int R=5, STEPS=24, ALL;bool full_repair=false;
vector<vector<int>> I(256), inc(256);
struct Cfg { int q,h,m; bool operator==(const Cfg&o)const{return tie(q,h,m)==tie(o.q,o.h,o.m);} };
struct Case { int mask; vector<Cfg> hist; };
vector<Case> oldcases[512];
int dead, dest;
Row row0,row1;
map<int,Row> edits;
Row get(int k){if(edits.count(k))return edits[k]; if(k/2==dest)return k%2?row1:row0; Row t=T[k]; if(t.q==dead)t.q=dest;return t;}
bool meet(int k,int mask,const vector<Cfg>& hist,Row first,bool useEdits=false) {
 Cfg c={k/2,0,mask};
 for(int s=1;s<=STEPS;s++){
  if(abs(c.h)>R || c.q==254 || c.q==dead)return false;
  int key=c.q*2+((c.m>>(c.h+R))&1); Row t=s==1?first:get(key);
  c.m=(c.m&~(1<<(c.h+R)))|(t.w<<(c.h+R));c.h+=t.d;c.q=t.q;
  if(c.q!=dead&&c.q!=dest)for(const Cfg&o:hist)if(c==o)return true;
 }
 return false;
}
bool check(int k,Row first){for(const auto& c:oldcases[k])if(!meet(k,c.mask,c.hist,first))return false;return true;}
void prepare(int k){
 oldcases[k].clear();
 for(int m:I[k/2])if(((m>>R)&1)==k%2){Case rec;rec.mask=m;Cfg c={k/2,0,m};
  for(int s=1;s<=STEPS;s++){if(abs(c.h)>R||c.q==254)break;Row t=T[c.q*2+((c.m>>(c.h+R))&1)];c.m=(c.m&~(1<<(c.h+R)))|(t.w<<(c.h+R));c.h+=t.d;c.q=t.q;rec.hist.push_back(c);}
  oldcases[k].push_back(rec);
 }
}
int main(int argc,char**argv){
 if(argc<2){cerr<<"table [radius] [steps] [full-repair]\n";return 2;}if(argc>2)R=stoi(argv[2]);if(argc>3)STEPS=stoi(argv[3]);if(argc>4)full_repair=string(argv[4])=="full-repair";ALL=1<<(2*R+1);
 ifstream f(argv[1]);string line;bool present[256]={};
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,n;char d;s>>q>>b>>w>>d>>n;T[q*2+b]={w,d=='R'?1:-1,n};present[q]=true;}
 for(int q=0;q<256;q++)if(present[q])states.push_back(q);
 vector<vector<uint8_t>> seen(256,vector<uint8_t>(ALL));vector<pair<int,int>> todo;
 for(int m=0;m<ALL;m++){seen[95][m]=1;todo.push_back({95,m});}
 for(size_t i=0;i<todo.size();i++){auto[q,m]=todo[i];if(q==254)continue;Row t=T[q*2+((m>>R)&1)];m=(m&~(1<<R))|(t.w<<R);int n=t.d==1?m>>1:(m<<1)&(ALL-1);int bit=t.d==1?1<<(2*R):1;for(int z:{n,n|bit})if(!seen[t.q][z]){seen[t.q][z]=1;todo.push_back({t.q,z});}}
 for(int q:states){for(int m=0;m<ALL;m++)if(seen[q][m])I[q].push_back(m);for(int b=0;b<2;b++)inc[T[q*2+b].q].push_back(q*2+b);}
 cerr<<"Invariant radius "<<R<<" patterns "<<todo.size()<<"\n";
 for(int q:states)for(int b=0;b<2;b++)prepare(q*2+b);
 int tested=0,qpass=0,surv=0;map<int,int> qs;
 for(int dead_value:states){dead=dead_value;if(dead==95||dead==96)continue;
  for(int dest_value:states){dest=dest_value;if(dest==dead||dest==95||dest==96)continue;
   for(int variant=1;variant<4;variant++){
    row0=(variant&1)?T[dead*2]:T[dest*2];row1=(variant&2)?T[dead*2+1]:T[dest*2+1];
    if(row0.q==dead)row0.q=dest;if(row1.q==dead)row1.q=dest;
    if(row0==T[dest*2]&&row1==T[dest*2+1])continue;
    tested++;edits.clear();bool ok=true;
    for(int k:inc[dead])if(k/2!=dead&&k/2!=dest){Row first=T[k];first.q=dest;if(!check(k,first)){ok=false;break;}}
    if(!ok)continue;qpass++;qs[dead]++;
    // Repair old entries into reused state, allowing target changes first.
    for(int k:inc[dest])if(k/2!=dead&&k/2!=dest){if(check(k,T[k]))continue;bool fixed=false;
     for(int phase=0;phase<(full_repair?4:1)&&!fixed;phase++){
      Row basis=T[k];if(phase&1)basis.w^=1;if(phase&2)basis.d=-basis.d;
      for(int q:states){if(q==dead)continue;Row first=basis;first.q=q;if(check(k,first)){edits[k]=first;fixed=true;break;}}
     }
     if(!fixed){ok=false;break;}
    }
    if(!ok)continue;
    vector<int> es=inc[dead];es.insert(es.end(),inc[dest].begin(),inc[dest].end());
    for(int k:es)if(k/2!=dead&&k/2!=dest)if(!check(k,get(k))){ok=false;break;}
    if(!ok)continue;
    surv++;cout<<"SURVIVOR dead "<<dead<<" dest "<<dest<<" variant "<<variant<<"\n";
    cout<<"  rows "<<row0.w<<" "<<row0.d<<" "<<row0.q<<" ; "<<row1.w<<" "<<row1.d<<" "<<row1.q<<"\n";
    for(auto[k,t]:edits)cout<<"  repair "<<k/2<<" "<<k%2<<" = "<<t.w<<" "<<t.d<<" "<<t.q<<"\n";
    cout.flush();
   }
  }
 }
 cerr<<"Tested "<<tested<<" qpass "<<qpass<<" survivors "<<surv<<"\n";
 for(auto[q,n]:qs)cerr<<q<<":"<<n<<" ";cerr<<"\n";
}
