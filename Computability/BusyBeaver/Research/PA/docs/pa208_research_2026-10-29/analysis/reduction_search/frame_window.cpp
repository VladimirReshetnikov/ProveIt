#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Row { int w,d,z; };
int main(int argc,char**argv){
 if(argc<5)return 2;
 ifstream f(argv[1]);Row tm[512][2];bool active[512]={};
 string s;while(getline(f,s)){if(s.empty()||s[0]=='#')continue;stringstream ss(s);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;tm[q][b]={w,d=='R'?1:-1,z};active[q]=true;}
 int r=stoi(argv[3]),bits=2*r+1,count=1<<bits,mask=count-1;
 int mode=stoi(argv[4]);bool blank=mode==1;vector<unsigned char> seen(512*count);vector<uint32_t> queue;
 auto add=[&](int q,int x){int k=q*count+x;if(!seen[k]){seen[k]=1;queue.push_back(k);}};
 if(mode==2){ifstream sf(argv[5]);string address,op;int arg;while(sf>>address>>op>>arg){int bits=1<<(r-1);for(int j=0;j<=r;j++)if(j<(int)address.size()&&address[j]=='1')bits|=1<<(r+j);add(84,bits);}}
 else if(blank)add(0,0);else for(int x=0;x<count;x++)add(0,x);
 for(size_t i=0;i<queue.size();i++){
  int k=queue[i],q=k/count,x=k&mask,b=(x>>r)&1;Row a=tm[q][b];if(a.z==254||(mode==2&&a.z==84))continue;
  x=(x&~(1<<r))|(a.w<<r);int y,edge;
  if(a.d==1){y=x>>1;edge=1<<(2*r);}else{y=(x<<1)&mask;edge=1;}
  add(a.z,y);add(a.z,y|edge);
 }
 ofstream o(argv[2],ios::binary);o.write((char*)seen.data(),seen.size());
 cout<<"radius "<<r<<" initial "<<(blank?"blank":"arbitrary")<<" reachable "<<queue.size()<<endl;
 for(int q=0;q<512;q++)if(active[q]){int c=0,c0=0;for(int x=0;x<count;x++)if(seen[q*count+x]){c++;if(!((x>>r)&1))c0++;}cout<<q<<' '<<c<<' '<<c0<<'\n';}
}
