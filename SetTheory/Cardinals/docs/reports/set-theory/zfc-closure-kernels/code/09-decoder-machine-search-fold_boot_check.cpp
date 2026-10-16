#include <bits/stdc++.h>
using namespace std;struct Tr{int w,d,n;};
int main(int argc,char**argv){
 Tr T0[1024][2]{};bool row[1024]{};ifstream in(argv[1]);string line;int maxq=0;
 while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,n;char d;s>>q>>b>>w>>d>>n;T0[q][b]={w,d=='R'?1:-1,n};row[q]=1;maxq=max(maxq,q);}
 ifstream pin(argv[2]);vector<pair<int,int>>pairs;int p,r;while(pin>>p>>r)pairs.push_back({p,r});
 ifstream tin(argv[3]);vector<int>rel;int j;while(tin>>j)rel.push_back(j);
 int LIMIT=argc>4?atoi(argv[4]):1000000;const int SZ=40000,Z=10000;vector<unsigned char>a(SZ);long long steps=0;
 for(auto[dead,to]:pairs){
  Tr T[1024][2];copy(&T0[0][0],&T0[0][0]+2048,&T[0][0]);for(int q=0;q<=maxq;q++)if(row[q])for(int b=0;b<2;b++)if(T[q][b].n==dead)T[q][b].n=to;
  fill(a.begin(),a.end(),0);int q=0,h=Z,ones=0;
  for(int t=0;t<LIMIT;t++){
   if(q==254||q==dead||!row[q]||h<2||h>=SZ-2)break;
   Tr z=T[q][a[h]];ones+=z.w-a[h];a[h]=z.w;h+=z.d;q=z.n;++steps;
   if(q==96&&ones==(int)rel.size()){
    bool ok=true;for(int x:rel){if(h+x<0||h+x>=SZ||a[h+x]!=1){ok=false;break;}}
    if(ok){cout<<dead<<" "<<to<<" "<<t+1<<" "<<h-Z<<endl;break;}
   }
  }
 }
 cerr<<"checked "<<pairs.size()<<" folds, "<<steps<<" steps"<<endl;
}
