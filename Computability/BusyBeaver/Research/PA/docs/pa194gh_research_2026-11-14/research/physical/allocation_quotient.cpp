#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};
int main(int argc,char**argv){
 array<A,2>base[3000];bool ex[3000]={};vector<int>qs;ifstream f(argv[1]);int q,b,w,n;char d;
 while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]={w,d=='R'?1:-1,n};}
 vector<int>SK={51,36,25,48,32,33,22,55,60};set<int>BOX={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 map<int,int>ix;for(int q:qs)ix[q]=ix.size();int size=qs.size(),halt=size;ix[254]=halt;
 struct E{int src,bit,slot;};vector<E>edits;array<A,2>rows[300];
 for(int q:qs)for(int b=0;b<2;b++){
  A a=base[q][b];int r=find(SK.begin(),SK.end(),a.n)-SK.begin();
  if(!BOX.count(q)&&r<9)edits.push_back({ix[q],b,r});
  rows[ix[q]][b]={a.w,a.d,ix[a.n]};
 }
 vector<int>p={0,1,2,3,4,5,6,7,8};long layouts=0,hits=0;int best=size;auto t0=chrono::steady_clock::now();bool fix=argc<3||stoi(argv[2]);
 do{
  if(fix&&p[6]!=6)continue;layouts++;
  for(E e:edits)rows[e.src][e.bit].n=ix[SK[p[e.slot]]];
  vector<int>cl(size+1);cl[halt]=1;int classes=1;
  for(int iter=0;iter<size;iter++){
   map<array<int,6>,int>sig;vector<int>nc(size+1);nc[halt]=-1;
   for(int q=0;q<size;q++){A a=rows[q][0],b=rows[q][1];array<int,6>s={a.w,a.d,cl[a.n],b.w,b.d,cl[b.n]};if(!sig.count(s))sig[s]=sig.size();nc[q]=sig[s];}
   int count=sig.size();nc[halt]=count;
   bool done=count==classes;cl=move(nc);classes=count;if(done)break;
  }
  if(classes<size){hits++;cout<<"{\"permutation\":[";for(int i=0;i<9;i++){if(i)cout<<',';cout<<p[i];}cout<<"],\"classes\":"<<classes<<",\"pairs\":[";bool first=true;for(int i=0;i<size;i++)for(int j=i+1;j<size;j++)if(cl[i]==cl[j]){if(!first)cout<<',';first=false;cout<<'['<<qs[i]<<','<<qs[j]<<']';}cout<<"]}"<<endl;best=min(best,classes);}
 }while(next_permutation(p.begin(),p.end()));
 cerr<<"layouts "<<layouts<<" hits "<<hits<<" best "<<best<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<"\n";
}
