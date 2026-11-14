#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){
 if(argc<4)return 1;ifstream f(argv[1]);int R=stoi(argv[2]),W=2*R+1,P=1<<W;string out=argv[3],line;map<int,array<array<int,3>,2>>t;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;t[q][b]={w,d=='R'?1:-1,z};}
 vector<int>labels;map<int,int>index;for(auto &[q,v]:t){index[q]=labels.size();labels.push_back(q);}int N=labels.size();vector<unsigned char>seen(N*P);vector<unsigned int>todo;todo.reserve(N*P);
 auto add=[&](int q,int p){int v=q*P+p;if(!seen[v]){seen[v]=1;todo.push_back(v);}};
 if(argc>4) for(int p=0;p<P;++p) add(index[0],p); else add(index[0],0);
 // Only blank initial window; arbitrary boundary bits safely overapproximate blank execution.
 for(size_t i=0;i<todo.size();++i){int v=todo[i],q=v/P,p=v%P;auto tr=t[labels[q]][(p>>R)&1];auto it=index.find(tr[2]);if(it==index.end())continue;
  int a=(p&~(1<<R))|(tr[0]<<R);int b;
  if(tr[1]==1){b=a>>1;add(it->second,b);add(it->second,b|(1<<(W-1)));}
  else {b=(a<<1)&(P-1);add(it->second,b);add(it->second,b|1);}
 }
 ofstream o(out,ios::binary);o.write((char*)seen.data(),seen.size());ofstream meta(out+".meta");meta<<R<<" "<<P<<" "<<N<<"\n";for(int i=0;i<N;++i){int c=0;for(int p=0;p<P;++p)c+=seen[i*P+p];meta<<labels[i]<<" "<<c<<"\n";}cerr<<"Reached "<<todo.size()<<" / "<<N*P<<"\n";
}
