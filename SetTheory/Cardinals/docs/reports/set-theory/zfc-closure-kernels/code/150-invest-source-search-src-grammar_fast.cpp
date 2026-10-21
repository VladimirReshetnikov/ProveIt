#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>
using namespace std;
int n;
bool geometric=false;
vector<int> atoms, req;
vector<vector<pair<int,int>>> prod, parents;
vector<uint8_t> initial;
long long checks=0;
bool viable(const vector<int>& base,int add,int del1,int del2=-1){
 ++checks;
 if(geometric){
  vector<uint8_t> lead(n,255);for(int x:atoms)lead[x]=0;bool added=false;
  auto visit=[&](int x){if(x<0)return;for(auto[a,b]:prod[x])if(lead[a]<6&&lead[b]<7)lead[x]=min<int>(lead[x],lead[a]+1);};
  for(int x:base){if(!added&&add<x){visit(add);added=true;}if(x!=del1&&x!=del2)visit(x);}if(!added)visit(add);
  for(int x:req)if(lead[x]>6)return false;return true;
 }
 auto good=initial;bool added=false;
 auto visit=[&](int x){if(x<0)return;for(auto [a,b]:prod[x])if(good[a]&&good[b]){good[x]=1;return;}};
 for(int x:base){if(!added&&add<x){visit(add);added=true;}if(x!=del1&&x!=del2)visit(x);}
 if(!added)visit(add);
 for(int x:req)if(!good[x])return false;
 return true;
}
string key(const vector<int>& v){return string(reinterpret_cast<const char*>(v.data()),v.size()*sizeof(int));}
 vector<int> change(const vector<int>& st,int add,int del1,int del2=-1){vector<int> out;for(int x:st)if(x!=del1&&x!=del2)out.push_back(x);if(add>=0)out.push_back(add);sort(out.begin(),out.end());return out;}
int main(int argc,char**argv){
 if(argc<3){cerr<<"model out [width] [seconds] [barrier] [geometric] [levels]\n";return 2;}
 int width=argc>3?stoi(argv[3]):100;double budget=argc>4?stod(argv[4]):180;int barrier=argc>5?stoi(argv[5]):0;geometric=argc>6&&stoi(argv[6]);int levels=argc>7?stoi(argv[7]):1000;
 ifstream f(argv[1]);int na,nb,nr;f>>n>>na>>nb>>nr;atoms.resize(na);vector<int> base(nb);req.resize(nr);for(int&x:atoms)f>>x;for(int&x:base)f>>x;for(int&x:req)f>>x;
 prod.resize(n);parents.resize(n);for(int j=0;j<n;++j){int z;f>>z;while(z--){int a,b;f>>a>>b;prod[j].push_back({a,b});parents[a].push_back({j,b});parents[b].push_back({j,a});}}
 initial.assign(n,0);for(int x:atoms)initial[x]=1;vector<uint8_t> required(n);for(int x:req)required[x]=1;
 unordered_set<string> seen;seen.insert(key(base));vector<vector<int>>frontier={base};mt19937 rng(217204);auto start=chrono::steady_clock::now();ofstream log(string(argv[2])+".log");ofstream samples(string(argv[2])+".samples");
 for(int level=0;level<levels;++level){
  vector<vector<int>>cand;
  for(const auto&st:frontier){
   auto used=initial;for(int x:st)used[x]=1;vector<int>adds;
   for(int ad=0;ad<n;++ad)if(!used[ad]){
    bool child=false,parent=false;for(auto [x,y]:prod[ad])if(used[x]&&used[y]){child=true;break;}
    if(!child)continue;for(auto [x,y]:parents[ad])if(used[x]&&used[y]){parent=true;break;}if(parent)adds.push_back(ad);
   }
   if(int(st.size())>nb)for(int rm:st)if(!required[rm]&&viable(st,-1,rm)){
    auto z=change(st,-1,rm);if(seen.insert(key(z)).second)cand.push_back(move(z));
   }
   for(int ad:adds){
    if(int(st.size())<nb+barrier){auto z=change(st,ad,-1);if(seen.insert(key(z)).second)cand.push_back(move(z));}
    vector<int>drops;
    for(int rm:st)if(!required[rm]&&viable(st,ad,rm)){
     drops.push_back(rm);auto z=change(st,ad,rm);if(seen.insert(key(z)).second)cand.push_back(move(z));
    }
    for(int i=0;i<int(drops.size());++i)for(int j=i+1;j<int(drops.size());++j)if(viable(st,ad,drops[i],drops[j])){
     auto z=change(st,ad,drops[i],drops[j]);if(int(z.size())<nb){ofstream out(argv[2]);for(int x:z)out<<x<<' ';out<<'\n';cout<<"HIT "<<z.size()<<" level "<<level<<" checks "<<checks<<endl;return 0;}
     if(seen.insert(key(z)).second)cand.push_back(move(z));
    }
   }
  }
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  log<<level<<' '<<cand.size()<<' '<<seen.size()<<' '<<checks<<' '<<elapsed<<endl;cout<<level<<' '<<cand.size()<<' '<<seen.size()<<' '<<checks<<' '<<elapsed<<endl;
  if(cand.empty()||elapsed>budget)break;
  shuffle(cand.begin(),cand.end(),rng);
  {int collected=0;for(const auto&z:cand)if(int(z.size())==nb&&collected++<40){for(int x:z)samples<<x<<' ';samples<<'\n';}samples.flush();}
  if(barrier){vector<vector<int>>next;for(int cost=nb;cost<=nb+barrier;++cost){int count=0;for(auto&z:cand)if(int(z.size())==cost&&count++<width/(barrier+1))next.push_back(move(z));}frontier=move(next);}
  else{if(int(cand.size())>width)cand.resize(width);frontier=move(cand);}
 }
 cout<<"NO_HIT\n";
}
