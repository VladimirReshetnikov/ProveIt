#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
#include <string>
#include <cstdint>
using namespace std;
struct Row{string op;int arg,z,p;};
int main(int argc,char**argv){ifstream f(argv[1]);vector<Row> rows;Row a;while(f>>a.op>>a.arg>>a.z>>a.p)rows.push_back(a);int count=rows.size();vector<uint8_t> seen(count*512);vector<uint32_t> queue;
auto add=[&](int i,int v){if(i<0)return;int k=i*512+v;if(!seen[k]){seen[k]=1;queue.push_back(k);}};add(0,1);
for(size_t at=0;at<queue.size();at++){int key=queue[at],i=key/512,v=key%512;Row a=rows[i];if(a.op=="CI")add(a.z,v|(1<<a.arg));else if(a.op=="CD"){if(v&(1<<a.arg)){add(a.p,v&~(1<<a.arg));add(a.p,v);}else add(a.z,v);}else if(a.op!="CH")add(a.z,v);}
ofstream o(argv[2],ios::binary);o.write((char*)seen.data(),seen.size());cout<<"abstract_configurations "<<queue.size()<<endl;
for(int i=0;i<count;i++){int un=0,in=511,n=0;for(int v=0;v<512;v++)if(seen[i*512+v]){n++;un|=v;in&=v;}cout<<i<<' '<<n<<' '<<(511^un)<<' '<<in<<'\n';}}
