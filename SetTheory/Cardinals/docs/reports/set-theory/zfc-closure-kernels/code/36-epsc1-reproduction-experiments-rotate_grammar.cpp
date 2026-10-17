// Exact-word reassociation with globally shared canonical substrings.
// The emitted grammar is checked separately; this search is not trusted.
#include <algorithm>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>
using namespace std;
struct Node { int len, fixed, depth, split; vector<pair<int,int>> cuts; };
vector<Node> a;
vector<int> seen, ds, active;
int epoch=0, root, base, framework, fixedDepth, rootExtra, maxDepth;
int visit(int q) {
    if(seen[q]==epoch) return ds[q];
    seen[q]=epoch;
    if(a[q].fixed) return ds[q]=a[q].depth;
    active.push_back(q);
    auto [l,r]=a[q].cuts[a[q].split-1];
    int d=visit(l)+1;visit(r);maxDepth=max(maxDepth,d);
    return ds[q]=d;
}
int evaluate() {
    ++epoch;active.clear();maxDepth=fixedDepth;
    int d=visit(root);maxDepth=max(maxDepth,d+rootExtra);
    return base+framework+int(active.size())+maxDepth;
}
int main(int argc,char**argv) {
    if(argc<5){cerr<<"input output iterations seed\n";return 2;}
    ifstream in(argv[1]);int n;in>>n>>root>>base>>framework>>fixedDepth>>rootExtra;
    a.resize(n);seen.resize(n);ds.resize(n);
    for(auto &v:a){in>>v.len>>v.fixed>>v.depth>>v.split;
        v.cuts.resize(max(0,v.len-1));for(auto &p:v.cuts)in>>p.first>>p.second;}
    if(!in){cerr<<"bad input\n";return 2;}
    long long iterations=stoll(argv[3]);mt19937_64 rng(stoull(argv[4]));
    auto unit=[&](){return (rng()>>11)*0x1.0p-53;};
    int cost=evaluate(), best=cost;
    vector<int> initial(n), bestSplits(n);
    for(int q=0;q<n;++q)initial[q]=bestSplits[q]=a[q].split;
    auto save=[&](long long step){ofstream o(argv[2]);o<<best<<' '<<n<<'\n';
        for(int q=0;q<n;++q)o<<bestSplits[q]<<'\n';
        cerr<<"step="<<step<<" states="<<best<<" nodes="<<(base+active.size())<<" depth="<<maxDepth<<'\n';};
    save(0);
    for(long long it=1;it<=iterations;++it) {
        if(it%100000==0){for(int q=0;q<n;++q)a[q].split=(rng()%4?bestSplits[q]:initial[q]);cost=evaluate();}
        int q=active[rng()%active.size()], old=a[q].split;
        auto [l,r]=a[q].cuts[old-1];
        bool left=(rng()&1);
        int changed=-1, oldChild=-1;
        if(left && !a[l].fixed) {
            int la=a[l].split; int newR=a[q].cuts[la-1].second;
            a[q].split=la;
            if(seen[newR]!=epoch && !a[newR].fixed){changed=newR;oldChild=a[newR].split;a[newR].split=old-la;}
        } else if(!left && !a[r].fixed) {
            int rb=a[r].split;int newL=a[q].cuts[old+rb-1].first;
            a[q].split=old+rb;
            if(seen[newL]!=epoch && !a[newL].fixed){changed=newL;oldChild=a[newL].split;a[newL].split=old;}
        } else {continue;}
        int nc=evaluate();
        double cycle=double(it%100000)/100000.;
        double temp=0.06+0.60*(1.0-cycle)*(1.0-cycle);
        if(nc<=cost || unit()<exp(double(cost-nc)/temp)) cost=nc;
        else {a[q].split=old;if(changed>=0)a[changed].split=oldChild;cost=evaluate();}
        if(cost<best){best=cost;for(int j=0;j<n;++j)bestSplits[j]=a[j].split;save(it);}
    }
    for(int q=0;q<n;++q)a[q].split=bestSplits[q];
    cost=evaluate();if(cost!=best)return 3;save(iterations);
}
