// Positive controls for the literal frame detector used in the startup screen.
// Compile with -DORIGINAL_DETECTOR to replay the inherited 13-one threshold.
#define main inherited_search_main
#ifdef ORIGINAL_DETECTOR
#include "quad_allframes.cpp"
#else
#include "quad_firstwrite.cpp"
#endif
#undef main

void reset_detector(int pc, const string &path) {
    memset(base,0,sizeof(base)); memset(row,0,sizeof(row));
    memset(ex,0,sizeof(ex)); qs.clear(); es.clear();
    seeds.clear(); trie.assign(1,{-1,-1}); leaf.assign(1,-1);
    ticks=runs=hits=limits=halts=rays=0; BOUND=200000;
    int node=0;
    for(char ch:path) {
        int b=ch-'0';
        if(trie[node][b]<0) {
            trie[node][b]=trie.size(); trie.push_back({-1,-1});
            leaf.push_back(-1);
        }
        node=trie[node][b];
    }
    leaf[node]=0; seeds.push_back({pc,path,511});
}

void install(int q,int b,int w,int d,int n) {
    row[q][b]={w,d,n}; base[q][b]=row[q][b];
    if(!ex[q])qs.push_back(q);
    ex[q]=true;
}

string capture_run(int start,int &result) {
    ostringstream output;
    auto *old=cout.rdbuf(output.rdbuf());
    result=simulate(start,-1,-1);
    cout.rdbuf(old);
    return output.str();
}

int main(int argc,char **argv) {
    if(argc!=2) {cerr<<"primary194.native.tm required\n";return 2;}
    reset_detector(25,"100000");
#ifndef ORIGINAL_DETECTOR
    HEADER_MIN=48;
#endif
    ifstream f(argv[1]); int q,b,w,n; char dir;
    while(f>>q>>b>>w>>dir>>n)install(q,b,w,dir=='R'?1:-1,n);
    int result=0;
    string primary=capture_run(74,result);
#ifdef ORIGINAL_DETECTOR
    const string primary_time="\"steps\":24866,";
#else
    const string primary_time="\"steps\":58154,";
#endif
    if(result!=1 || primary.find(primary_time)==string::npos ||
       primary.find("\"head\":-2,")==string::npos ||
       primary.find("\"pc\":25,")==string::npos) {
        cerr<<"Primary positive control failed: "<<primary;return 1;
    }
    cout<<"PRIMARY_POSITIVE_CONTROL "<<primary;

    // Diagnostic writer. It constructs precisely twelve ones: a left marker,
    // right delimiter, and ten zero-valued unary blocks, at a source frame
    // for site 0/path000000, header distance48. It is NOT a consistency machine.
    reset_detector(0,"000000");
    set<int> target{0,49,51,53,55,57,59,61,63,65,67,69};
    vector<pair<int,int>> actions;
    actions.push_back({1,1});                 // from position0 to1
    for(int p=1;p<=69;p++)actions.push_back({target.count(p)?1:0,1});
    for(int p=70;p>=2;p--)actions.push_back({target.count(p)?1:0,-1});
    for(size_t i=0;i<actions.size();i++) {
        int state=i==0?74:499+i;
        int next=i+1==actions.size()?84:500+i;
        for(int bit=0;bit<2;bit++)
            install(state,bit,actions[i].first,actions[i].second,next);
    }
    install(84,0,0,-1,254); install(84,1,1,-1,254);
    string tiny=capture_run(74,result);
#ifdef ORIGINAL_DETECTOR
    if(result!=0 || hits!=0 || halts!=1) {
        cerr<<"Original-threshold negative control failed: "<<tiny;return 1;
    }
    cout<<"TWELVE_ONE_CONTROL_REJECTED_BY_OLD_THRESHOLD\n";
#else
    const string expected_ones="\"ones\":[0,49,51,53,55,57,59,61,63,65,67,69]";
    if(result!=1 || tiny.find("\"steps\":139,")==string::npos ||
       tiny.find("\"pc\":0,")==string::npos || tiny.find(expected_ones)==string::npos) {
        cerr<<"Twelve-one positive control failed: "<<tiny;return 1;
    }
    cout<<"TWELVE_ONE_POSITIVE_CONTROL "<<tiny;
#endif
    cout<<"PASS\n";
}
