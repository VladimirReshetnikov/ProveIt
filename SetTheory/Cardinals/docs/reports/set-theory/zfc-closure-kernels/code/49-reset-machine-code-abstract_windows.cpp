// Compact exact fixed point for the finite-window abstraction.
// Both newly exposed exterior bits are admitted after every shift.
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Edge {int w,d,t;};
int main(int argc,char**argv) {
    if(argc!=4) {cerr<<"input-with-table output new-radius\n";return 2;}
    ifstream in(argv[1]);int n,oldR,k;in>>n>>oldR>>k;
    int r=atoi(argv[3]),width=2*r+1;
    if(!in||n<2||n>1000||r<1||r>10||width+10>=32)return 3;
    vector<array<Edge,2>> table(n);
    for(int q=0;q<n;++q)for(int b=0;b<2;++b) {
        Edge& e=table[q][b];in>>e.w>>e.d>>e.t;
        if(e.w<0||e.w>1||(e.d!=-1&&e.d!=1)||e.t<0||e.t>n)return 4;
    }
    if(!in)return 5;
    const uint32_t patterns=1u<<width,mask=patterns-1;
    vector<uint8_t> seen(size_t(n+1)*patterns,0);
    vector<uint32_t> queue{0};seen[0]=1;
    for(size_t i=0;i<queue.size();++i) {
        uint32_t code=queue[i],q=code>>width,p=code&mask;
        if(q==uint32_t(n))continue;
        const Edge e=table[q][(p>>r)&1];
        p=(p&~(1u<<r))|(uint32_t(e.w)<<r);
        uint32_t base=e.d==1?p>>1:(p<<1)&mask;
        uint32_t extra=e.d==1?1u<<(width-1):1u;
        for(uint32_t nextP:{base,base|extra}) {
            uint32_t next=(uint32_t(e.t)<<width)|nextP;
            if(!seen[next]){seen[next]=1;queue.push_back(next);}
        }
    }
    ofstream out(argv[2]);out<<n<<' '<<r<<' '<<k<<'\n';
    for(int q=0;q<n;++q)for(int b=0;b<2;++b) {
        const Edge e=table[q][b];out<<e.w<<' '<<e.d<<' '<<e.t<<'\n';
    }
    for(int q=0;q<=n;++q) {
        uint32_t count=0;size_t base=size_t(q)*patterns;
        for(uint32_t p=0;p<patterns;++p)count+=seen[base+p];
        out<<count;
        for(uint32_t p=0;p<patterns;++p)if(seen[base+p])out<<' '<<p;
        out<<'\n';
    }
    cout<<"{\"radius\":"<<r<<",\"abstract_pairs\":"<<queue.size()<<",\"dense_bytes\":"<<seen.size()<<"}\n";
    return out?0:6;
}
