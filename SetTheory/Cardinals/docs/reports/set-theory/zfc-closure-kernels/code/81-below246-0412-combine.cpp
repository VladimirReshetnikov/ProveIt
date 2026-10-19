#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
#include <sstream>
#include <functional>
#include <map>
using namespace std;
struct Row {int w,d,q;};
array<array<Row,2>,256>T;
struct Case{bitset<512>a,z;int q,h;};vector<Case>tests;
int main(int argc,char**argv){
 int removed=stoi(argv[4]);ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;
 vector<int> states;while(tf>>q>>b>>w>>d>>t){T[q][b]={w,d=='R'?1:-1,t};if(!b&&q!=removed)states.push_back(q);}
 ifstream cf(argv[2]);int n,k;while(cf>>n){Case c;for(int i=0;i<n;i++){cf>>k;c.a[k+128]=1;}cf>>c.q>>c.h>>n;c.h+=128;
 for(int i=0;i<n;i++){cf>>k;c.z[k+128]=1;}cf>>n;for(int i=0;i<n;i++)cf>>k;tests.push_back(c);}
 mt19937 rng(823765);shuffle(tests.begin(),tests.end(),rng);
 map<pair<int,int>,vector<Row>> choices;
 for(int q:states)for(int b=0;b<2;b++)if(T[q][b].q==removed)choices[{q,b}]={};
 ifstream ef(argv[3]);string line;while(getline(ef,line)){
  if(line.rfind("SURVIVOR",0)!=0)continue;
  int q,b,ow,od,ot,nw,nd,nt;char word[50];
  if(sscanf(line.c_str(),"SURVIVOR %d %d orig=%d %d %d new=%d %d %d",&q,&b,&ow,&od,&ot,&nw,&nd,&nt)!=8)continue;
  if(ot==removed&&q!=removed&&nt!=removed)choices[{q,b}].push_back({nw,nd,nt});
 }
 vector<pair<int,int>>keys;for(auto &it:choices){keys.push_back(it.first);cerr<<it.first.first<<"/"<<it.first.second<<" choices "<<it.second.size()<<endl;}
 size_t combos=0,hits=0,maxpass=0;vector<Row> chosen;
 function<void(int)> go=[&](int depth){
  if(depth<(int)keys.size()){
   auto key=keys[depth];auto original=T[key.first][key.second];for(auto row:choices[key]){T[key.first][key.second]=row;chosen.push_back(row);go(depth+1);chosen.pop_back();}T[key.first][key.second]=original;return;
  }
  combos++;size_t passed=0;
  for(auto &ex:tests){auto tape=ex.a;int q=96,h=128,visits=0;bool ok=false;
   for(int tick=0;tick<10000;tick++){
    if(h<0||h>=512||q==removed)break;
    auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q;
    if(q==254){ok=ex.q==254;break;}
    if(q==96){if(ex.q==96&&h==ex.h&&tape==ex.z){ok=true;break;}if(++visits>15)break;}
   }
   if(!ok)break;passed++;
  }
  maxpass=max(maxpass,passed);
  if(passed==tests.size()){
   hits++;cout<<"HIT";for(int i=0;i<(int)keys.size();i++)cout<<" ["<<keys[i].first<<","<<keys[i].second<<"]="<<chosen[i].w<<","<<chosen[i].d<<","<<chosen[i].q;cout<<endl;
  }
 };
 go(0);cerr<<"DONE combinations "<<combos<<" hits "<<hits<<" maxpassed "<<maxpass<<endl;
}
