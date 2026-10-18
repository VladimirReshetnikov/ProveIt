#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <unordered_map>
#include <cstring>
using namespace std;
struct Row{int w,d,t;};Row T[256][2],U[256][2];
int S[9]={60,44,31,56,38,40,28,64,69},IS[256];vector<int>states;
int main(int argc,char**argv){
 fill(IS,IS+256,-1);for(int i=0;i<9;i++)IS[S[i]]=i;
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,t;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&t);T[q][b]={w,d=='R'?1:0,t};if(b==0)states.push_back(q);}
 vector<pair<int,int>>entries;
 for(int q:states)for(int b:{0,1})if(IS[q]<0&&IS[T[q][b].t]>=0)entries.emplace_back(q,b);
 cerr<<"entries "<<entries.size()<<endl;
 array<int,9>P{0,1,2,3,4,5,6,7,8};long tried=0,pass=0,unreachable=0;int minreach=246;
 do {
  std::memcpy(U,T,sizeof(T));for(auto[q,b]:entries)U[q][b].t=S[P[IS[T[q][b].t]]];
  array<int,256>C{},D{};C[254]=1;int prev=-1,nc=2;
  for(int iter=0;iter<256;iter++){
   unordered_map<unsigned,int>seen;seen.reserve(512);nc=0;
   for(int q:states){auto a=U[q][0],b=U[q][1];unsigned sig=(((a.w*2+a.d)*4+b.w*2+b.d)*256+C[a.t])*256+C[b.t];auto[it,ok]=seen.emplace(sig,nc);if(ok)nc++;D[q]=it->second;}
   D[254]=nc;C=D;if(nc==prev)break;prev=nc;
  }
  bool reached[256]{};vector<int>stack{95};int nr=0;while(!stack.empty()){int q=stack.back();stack.pop_back();if(q==254||reached[q])continue;reached[q]=true;nr++;stack.push_back(U[q][0].t);stack.push_back(U[q][1].t);}minreach=min(minreach,nr);if(nr<246)unreachable++;tried++;
  if(nc<246){pass++;cout<<"PASS count "<<nc<<" perm";for(int x:P)cout<<" "<<x;cout<<" merges";for(int i=0;i<246;i++)for(int j=i+1;j<246;j++)if(C[states[i]]==C[states[j]])cout<<" "<<states[i]<<","<<states[j];cout<<endl;}
 }while(next_permutation(P.begin(),P.end()));
 cerr<<"tried "<<tried<<" pass "<<pass<<" permutations_with_unreachable_states "<<unreachable<<" minimum_graph_reachable "<<minreach<<endl;
}
