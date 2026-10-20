#include <bits/stdc++.h>
using namespace std;
struct Node{int op,arg,z,p;};
int main(int argc,char**argv){ifstream in(argv[1]);int n;in>>n;vector<Node>g(n);for(auto&v:g)in>>v.op>>v.arg>>v.z>>v.p;const int patterns=1<<18,words=patterns/64;vector<uint64_t>seen((size_t)n*words);vector<uint64_t>q;q.reserve(10000000);int current_source=-1;array<unordered_set<int>,4>external;auto put=[&](int i,int r){int ix=i==4567?0:i==4585?1:i==4599?2:i==4708?3:-1;if(ix>=0&&(current_source<i||current_source>=i+10))external[ix].insert(r);if(i<0)return;auto&x=seen[(size_t)i*words+r/64];uint64_t b=1ull<<(r%64);if(!(x&b)){x|=b;q.push_back((uint64_t)i<<18|r);}};put(0,3|(3<<8));vector<array<int,9>>masks(n);vector<array<int,2>>witness(n,array<int,2>{-1,-1});vector<int>counts(n);auto beg=chrono::steady_clock::now();size_t head=0;
while(head<q.size()){
 uint64_t v=q[head++];int i=v>>18,r=v&(patterns-1);auto a=g[i];current_source=i;counts[i]++;for(int j=0;j<9;j++)masks[i][j]|=1<<((r>>(2*j))&3);
 if(a.op!=2&&witness[i][0]<0)witness[i][0]=r;if(a.op==3)continue;if(a.op==0){put(a.z,r);continue;}int k=(r>>(2*a.arg))&3,base=r&~(3<<(2*a.arg));
 if(a.op==1){put(a.z,base|(min(k+1,3)<<(2*a.arg)));continue;}
 if(k==0){if(witness[i][0]<0)witness[i][0]=r;put(a.z,r);}else{if(witness[i][1]<0)witness[i][1]=r;put(a.p,base|((k-1)<<(2*a.arg)));if(k==3)put(a.p,r);}
 if(head%10000000==0)cerr<<"PROGRESS "<<head<<" "<<q.size()<<" "<<chrono::duration<double>(chrono::steady_clock::now()-beg).count()<<"\n";
 if(q.size()>100000000){cerr<<"CAP "<<head<<" "<<q.size()<<"\n";return 2;}
}
if(argc>4){ofstream selected(argv[4]);int sites[]={4567,4585,4599,4708};for(int k=0;k<4;k++)for(int r:external[k])selected<<sites[k]<<" "<<r<<"\n";}
if(argc>3){ofstream selected(argv[3]);for(auto v:q){int i=v>>18,r=v&(patterns-1);if(i==4567||i==4585||i==4599||i==4708)selected<<i<<" "<<r<<"\n";}}
ofstream out(argv[2]);int both=0,zero=0,pos=0;for(int i=0;i<n;i++){out<<i<<" "<<counts[i];for(int m:masks[i])out<<" "<<m;out<<" "<<witness[i][0]<<" "<<witness[i][1]<<"\n";if(g[i].op==2&&counts[i]){bool z=witness[i][0]>=0,p=witness[i][1]>=0;if(z&&p)both++;else if(z)zero++;else pos++;}}cerr<<"DONE patterns "<<q.size()<<" both "<<both<<" zero "<<zero<<" positive "<<pos<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-beg).count()<<"\n";
}
