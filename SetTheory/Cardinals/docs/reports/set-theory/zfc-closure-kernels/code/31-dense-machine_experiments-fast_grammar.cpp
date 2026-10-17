// Exact-word overlap-safe grammar search; source macros are closed RM programs.
// No logical row or theory formula is changed. Cost = reachable decision nodes
// plus 55 fixed framework states plus actual maximum consecutive-left depth.
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
using Pair=pair<int,int>;
vector<Pair> base;
vector<int> word;
uint64_t key(int a,int b){ return (uint64_t(uint32_t(a))<<32)|uint32_t(b); }
int evaluate(const vector<int>&seq,const vector<Pair>&gr){
 vector<Pair> ns=base;
 unordered_map<uint64_t,int> intern;
 for(int q=0;q<(int)base.size();++q)if(q==0||q>114)intern[key(base[q].first,base[q].second)]=q;
 auto pairnode=[&](int a,int b){uint64_t k=key(a,b);auto it=intern.find(k);if(it!=intern.end())return it->second;int id=ns.size();ns.emplace_back(a,b);intern[k]=id;return id;};
 vector<int> mapped(gr.size());
 auto mapid=[&](int a){return a>=300?mapped[a-300]:a;};
 for(int i=0;i<(int)gr.size();++i)mapped[i]=pairnode(mapid(gr[i].first),mapid(gr[i].second));
 int root=mapid(seq.back());for(int i=(int)seq.size()-2;i>=0;--i)root=pairnode(mapid(seq[i]),root);
 for(int q=0;q<(int)ns.size();++q)if(q==0||q>114){if(ns[q].first==1)ns[q].first=root;if(ns[q].second==1)ns[q].second=root;}
 vector<int> stack={0};vector<bool> seen(ns.size());int n=0,maxd=2;
 while(!stack.empty()){
  int q=stack.back();stack.pop_back();if(q<0||seen[q])continue;seen[q]=true;++n;
  int r=q,d=0;while(r>=0){++d;r=ns[r].first;}maxd=max(maxd,d);
  if(ns[q].first>=0)stack.push_back(ns[q].first);if(ns[q].second>=0)stack.push_back(ns[q].second);
 }
 return n+55+maxd;
}
int main(int argc,char**argv){
 if(argc!=5){cerr<<"usage: fast_grammar INPUT OUTPUT TRIALS SEED\n";return 1;}
 ifstream in(argv[1]);int n;in>>n;base.resize(n);for(auto &[a,b]:base)in>>a>>b;in>>n;word.resize(n);for(int&x:word)in>>x;
 uint64_t trials=stoull(argv[3]),seed=stoull(argv[4]);mt19937_64 rng(seed);
 const int M=1024*1024;vector<uint32_t> stamps(M);vector<int> counts(M);uint32_t stamp=0;
 int best=10000;ofstream out(argv[2]);
 for(uint64_t trial=0;trial<trials;++trial){
  vector<int>seq=word;vector<Pair>gr;int alpha=1<<((trial/4)%4);
  while(true){
   ++stamp;vector<int>keys;
   auto add=[&](int a,int b,int c){int k=a*1024+b;if(stamps[k]!=stamp){stamps[k]=stamp;counts[k]=0;keys.push_back(k);}counts[k]+=c;};
   for(int i=0;i+1<(int)seq.size();){
    if(seq[i]!=seq[i+1]){add(seq[i],seq[i+1],1);++i;}
    else{int j=i+2;while(j<(int)seq.size()&&seq[j]==seq[i])++j;add(seq[i],seq[i],(j-i)/2);i=j-1;}
   }
   vector<Pair>choices;double sum=0;
   for(int k:keys)if(counts[k]>=2){choices.emplace_back(k,counts[k]);double w=counts[k];for(int s=1;s<alpha;s*=2)w*=w;sum+=w;}
   if(choices.empty())break;
   double pick=double(rng()>>11)*(1.0/9007199254740992.0)*sum;int selected=choices.back().first;
   for(auto [k,count]:choices){double w=count;for(int s=1;s<alpha;s*=2)w*=w;if(pick<w){selected=k;break;}pick-=w;}
   int a=selected/1024,b=selected%1024;vector<int>next;for(int i=0;i<(int)seq.size();){if(i+1<(int)seq.size()&&seq[i]==a&&seq[i+1]==b){next.push_back(300+gr.size());i+=2;}else next.push_back(seq[i++]);}
   assert(seq.size()-next.size()>=2);seq=move(next);gr.emplace_back(a,b);
  }
  int cost=evaluate(seq,gr);
  if(cost<best){best=cost;
   out<<"{\"trial\":"<<trial<<",\"rng_seed\":"<<seed<<",\"cost\":"<<cost<<",\"alpha\":"<<alpha<<",\"residual\":[";
   for(int i=0;i<(int)seq.size();++i)out<<(i?",":"")<<seq[i];out<<"],\"grammar\":[";
   for(int i=0;i<(int)gr.size();++i)out<<(i?",":"")<<"["<<gr[i].first<<","<<gr[i].second<<"]";out<<"]}"<<endl;
   cerr<<"trial "<<trial<<" cost "<<cost<<endl;
  }
 }
 cerr<<"completed "<<trials<<" trials; best "<<best<<endl;
}
