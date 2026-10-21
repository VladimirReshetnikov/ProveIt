#include <bits/stdc++.h>
using namespace std;
struct Act{int w,d,z;};
struct Context{int word;vector<int>trace;};
struct Cas{int word;const vector<int>*trace;};
int enc(int q,int h,int w){return (q*15+h+7)*32768+w;}
int main(int argc,char**argv){
 ifstream in(argv[1]);int N;in>>N;vector<int> labels(N+1);for(int i=0;i<N;i++)in>>labels[i];labels[N]=254;vector<array<Act,2>>T(N);for(auto&rr:T)for(auto&a:rr)in>>a.w>>a.d>>a.z;vector<vector<Context>>I(N);for(auto&v:I){int n;in>>n;v.resize(n);for(auto&x:v)in>>x.word;}
 auto start=chrono::steady_clock::now();long long ntrace=0;
 for(int old=0;old<N;old++)for(auto&x:I[old]){int q=old,h=0,w=x.word;unordered_set<int>seen;for(int tick=0;tick<97;tick++){
  if(h < -7 || h > 7 || q>=N)break;int key=enc(q,h,w);if(!seen.insert(key).second)break;Act a=T[q][(w>>(h+7))&1];w=(w&~(1<<(h+7)))|(a.w<<(h+7));h+=a.d;q=a.z;if(h>=-7&&h<=7)x.trace.push_back(enc(q,h,w));}
 sort(x.trace.begin(),x.trace.end());x.trace.erase(unique(x.trace.begin(),x.trace.end()),x.trace.end());ntrace+=x.trace.size();}
 cerr<<"precomputed traces "<<ntrace<<"\n";

 struct Variant{int a,c;vector<Act>choices[4];};vector<Variant>O;map<int,int>index;for(int i=0;i<=N;i++)index[labels[i]]=i;index[500]=N+1;
 ifstream opts(argv[2]);string line;while(getline(opts,line)){istringstream ss(line);Variant v;ss>>v.a>>v.c;v.a=index.at(v.a);v.c=index.at(v.c);for(int j=0;j<4;j++){int n;ss>>n;for(int i=0;i<n;i++){Act a;ss>>a.w>>a.d>>a.z;a.z=index.at(a.z);v.choices[j].push_back(a);}}O.push_back(v);}
 mt19937 gen(216);for(auto &x:I)shuffle(x.begin(),x.end(),gen);long long attempts=0,passes=0;
 for(int vi=0;vi<(int)O.size();vi++){const auto&o=O[vi];for(auto a0:o.choices[0])for(auto a1:o.choices[1])for(auto h0:o.choices[2])for(auto h1:o.choices[3])for(int H=0;H<N;H++){
  if(H==o.a||H==o.c)continue;attempts++;auto phi=[&](int q){return q==o.c?o.a:(q==N+1?H:q);};vector<array<Act,2>>U=T;U[H]={h0,h1};U[o.a]={a0,a1};bool good=true;
  for(int old:{H,o.a,o.c}){for(const auto&x:I[old]){
   int q=phi(old),h=0,word=x.word;bool ok=false;
   for(int tick=0;tick<97;tick++){
    if(h < -7 || h > 7)break;int key=enc(q,h,word);
    if(tick&&(binary_search(x.trace.begin(),x.trace.end(),key)||(q==o.a&&binary_search(x.trace.begin(),x.trace.end(),enc(o.c,h,word))))){ok=true;break;}
    if(q>=N)break;Act z=U[q][(word>>(h+7))&1];word=(word&~(1<<(h+7)))|(z.w<<(h+7));h+=z.d;q=phi(z.z);
   }
   if(!ok){good=false;break;}
  }if(!good)break;}
  if(good){passes++;cout<<"FOUND variant "<<vi<<" keep "<<labels[o.a]<<" drop "<<labels[o.c]<<" H "<<labels[H]<<" rows";for(auto z:{a0,a1,h0,h1})cout<<" "<<z.w<<" "<<z.d<<" "<<(z.z==N+1?labels[H]:labels[z.z]);cout<<"\n"<<flush;}
 }}
 cerr<<"attempts "<<attempts<<" passes "<<passes<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
