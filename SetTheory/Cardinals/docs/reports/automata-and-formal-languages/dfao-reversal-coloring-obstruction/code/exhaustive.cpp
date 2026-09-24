// Exhaustive binary transformation/coloring orbits, C++17, n <= 4.
// Only reductions: interchange the two generators and rename output colors.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <stdexcept>
#include <vector>
using V = std::vector<int>;
int power(int b, int e) { int r=1; while(e--) r*=b; return r; }
V decode(int x, int n, int base) {
    V r(n); for(int i=0;i<n;++i) { r[i]=x%base; x/=base; } return r;
}
int encode(const V& x,int base) {
    int r=0; for(int i=int(x.size())-1;i>=0;--i) r=r*base+x[i]; return r;
}
void array(const V& x) {
    std::cout<<"["; for(size_t i=0;i<x.size();++i){if(i)std::cout<<",";std::cout<<x[i];}
    std::cout<<"]";
}
int main(int argc,char** argv) {
    int max_n=argc>1?std::atoi(argv[1]):4;
    if(max_n<2 || max_n>4) { std::cerr<<"Use 2 <= max_n <= 4.\n"; return 2; }
    std::cout<<"[\n"; bool first=true;
    for(int n=2;n<=max_n;++n) for(int k=2;k<=n;++k) {
        int nt=power(n,n), nc=power(k,n);
        std::vector<V> trans(nt), colors(nc);
        for(int t=0;t<nt;++t)trans[t]=decode(t,n,n);
        for(int c=0;c<nc;++c)colors[c]=decode(c,n,k);
        std::vector<V> next(nt,V(nc));
        for(int t=0;t<nt;++t)for(int c=0;c<nc;++c) {
            V d(n); for(int q=0;q<n;++q)d[q]=colors[c][trans[t][q]];
            next[t][c]=encode(d,k);
        }
        V representatives, word(n,0);
        std::function<void(int,int)> gen=[&](int i,int maximum) {
            if(i==n) { if(maximum==k-1)representatives.push_back(encode(word,k)); return; }
            for(int c=0;c<=std::min(maximum+1,k-1);++c){word[i]=c;gen(i+1,std::max(maximum,c));}
        };
        gen(1,0);
        std::vector<uint64_t> stamp(nc,0);
        V queue(nc); uint64_t epoch=0, cases=0, max_count=0;
        int best=0, ba=0, bb=0, bc=0;
        for(int a=0;a<nt;++a)for(int b=a;b<nt;++b)for(int initial:representatives) {
            ++epoch; ++cases; int head=0,tail=1; queue[0]=initial;stamp[initial]=epoch;
            while(head<tail) {
                int c=queue[head++];
                for(int d:{next[a][c],next[b][c]})if(stamp[d]!=epoch){
                    stamp[d]=epoch;queue[tail++]=d;
                }
            }
            if(tail>best){best=tail;ba=a;bb=b;bc=initial;max_count=1;}
            else if(tail==best)++max_count;
        }
        if(!first) { std::cout<<",\n"; }
        first=false;
        std::cout<<"  {\"n\":"<<n<<",\"k\":"<<k<<",\"maps\":"<<nt
                 <<",\"output_partitions\":"<<representatives.size()
                 <<",\"cases\":"<<cases<<",\"maximum\":"<<best
                 <<",\"maximizers_in_reduced_search\":"<<max_count<<",\"a\":";
        array(trans[ba]);std::cout<<",\"b\":";array(trans[bb]);
        std::cout<<",\"tau\":";array(colors[bc]);std::cout<<"}"<<std::flush;
    }
    std::cout<<"\n]\n";
}
