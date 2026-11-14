#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Act{int w,d,n;};
struct Case{int source,bit;vector<int8_t>tape;};
int main(int argc,char**argv){ifstream f(argv[1]);int n,x,rad,limit;f>>n>>x>>rad>>limit;vector<int>labels(n);for(auto&v:labels)f>>v;vector<array<Act,2>>old(n);for(auto&r:old)for(auto&a:r)f>>a.w>>a.d>>a.n;vector<array<vector<Case>,2>>cx(n);for(int q=0;q<n;q++)for(int b=0;b<2;b++){int k;f>>k;while(k--){Case c{q,b,{}};c.tape.resize(2*rad+1);for(auto&v:c.tape){int y;f>>y;v=y;}cx[q][b].push_back(c);}}
int hshare=lower_bound(labels.begin(),labels.end(),2037)-labels.begin();size_t hits=0,trials=0;
for(int q=0;q<n;q++)if(q!=x&&q!=hshare&&cx[q][0].size()&&cx[q][1].size()&&labels[q]!=113){
 auto mapq=[&](int v){return v==x?q:v;};vector<array<Act,2>>rows=old;for(auto&r:rows)for(auto&a:r)a.n=mapq(a.n);
 auto check=[&](const Case&c){Act target=old[c.source][c.bit];target.n=mapq(target.n);int h=rad,s=q,diff=0;array<int8_t,128>tape;copy(c.tape.begin(),c.tape.end(),tape.begin());
  for(int step=0;step<limit;step++){
   if(step&&h==rad+target.d&&s==target.n&&diff==int(target.w!=c.tape[rad])&&tape[rad]==target.w)return true;
   if(h<0||h>2*rad||tape[h]<0||s<0||s>=n||s==hshare)return false;
   Act a=rows[s][tape[h]];diff+=(a.w!=c.tape[h])-(tape[h]!=c.tape[h]);tape[h]=a.w;h+=a.d;s=a.n;
  }return false;};
 vector<Case>cases;
 for(int src:{x,q})for(int b=0;b<2;b++)if(cx[src][b].size())cases.push_back(cx[src][b].front());
 for(int src:{x,q})for(int b=0;b<2;b++)for(auto&c:cx[src][b])cases.push_back(c);
 vector<Act>acts;for(int w=0;w<2;w++)for(int d:{-1,1})for(int t=-1;t<n;t++)if(t!=x)acts.push_back({w,d,t});
 size_t best=0;
 for(auto&a0:acts)for(auto&a1:acts){
  rows[q][0]=a0;rows[q][1]=a1;trials++;size_t k=0;
  for(;k<cases.size();k++)if(!check(cases[k]))break;
  if(k>best)best=k;
  if(k==cases.size()){hits++;cout<<"HIT q "<<labels[q]<<" action0 "<<a0.w<<" "<<a0.d<<" "<<(a0.n<0?254:labels[a0.n])<<" action1 "<<a1.w<<" "<<a1.d<<" "<<(a1.n<0?254:labels[a1.n])<<" cases "<<cases.size()<<endl;}
 }
 cout<<"done donor "<<labels[q]<<" cases "<<cases.size()<<" best "<<best<<" trials "<<trials<<" hits "<<hits<<endl;
}
cout<<"DONE "<<trials<<" "<<hits<<endl;
}
