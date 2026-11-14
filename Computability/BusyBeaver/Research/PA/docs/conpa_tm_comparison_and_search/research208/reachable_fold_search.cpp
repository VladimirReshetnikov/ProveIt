#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Act{int w,d,n;};
int main(int argc,char**argv){ifstream f(argv[1]);int n,rad,limit;f>>n>>rad>>limit;vector<int>labels(n);for(auto&v:labels)f>>v;vector<array<Act,2>>rows(n);for(auto&r:rows)for(auto&a:r)f>>a.w>>a.d>>a.n;vector<array<vector<vector<int8_t>>,2>>cx(n);for(int q=0;q<n;q++)for(int b=0;b<2;b++){int k;f>>k;while(k--){vector<int8_t>tape(2*rad+1);for(auto&v:tape){int y;f>>y;v=y;}cx[q][b].push_back(move(tape));}}
size_t trials=0,found=0;
for(int q=0;q<n;q++)for(int bit=0;bit<2;bit++)if(cx[q][bit].size()){
 Act target=rows[q][bit];
 auto check=[&](const vector<int8_t>&src,Act act){int h=rad,s=q,diff=0;array<int8_t,128>tape;copy(src.begin(),src.end(),tape.begin());
  for(int step=0;step<limit;step++){
   if(step&&h==rad+target.d&&s==target.n&&diff==int(target.w!=src[rad])&&tape[rad]==target.w)return true;
   if(h<0||h>2*rad||tape[h]<0||s<0||s>=n)return false;
   Act a=step?rows[s][tape[h]]:act;diff+=(a.w!=src[h])-(tape[h]!=src[h]);tape[h]=a.w;h+=a.d;s=a.n;
  }return false;};
 vector<Act>options;for(int w=0;w<2;w++)for(int d:{-1,1})for(int t=-1;t<n;t++){
  Act a{w,d,t};trials++;bool ok=true;for(auto&c:cx[q][bit])if(!check(c,a)){ok=false;break;}if(ok)options.push_back(a);
 }
 cout<<labels[q]<<" "<<bit<<" "<<options.size();for(auto&a:options)cout<<" "<<a.w<<" "<<a.d<<" "<<(a.n<0?254:labels[a.n]);cout<<"\n";cout.flush();found+=options.size();
}
cerr<<"DONE trials "<<trials<<" options "<<found<<endl;
}
