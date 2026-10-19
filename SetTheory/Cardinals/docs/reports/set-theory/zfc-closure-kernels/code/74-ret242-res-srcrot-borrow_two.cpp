#include <array>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
using namespace std;
struct Row {int w,d,t;};
array<array<Row,2>,300> tab;
vector<int> qs;
bool run(int wt,int dt,int qt,int second,int target,int mask){
    constexpr int R=6,N=2*R+1;
    array<int,N> a{},b{};
    int m=mask;
    for(int p=-R;p<=R;p++){
        int v;
        if(p==0)v=1;else if(p==-1)v=0;else if(p==-2)v=second;
        else {v=m&1;m>>=1;}
        a[p+R]=b[p+R]=v;
    }
    int q=qt,h=dt;a[R]=wt;
    for(int step=0;step<80;step++){
        if(q==target && h==1 && a==b)return true;
        if(q==254 || q==171 || h<-R || h>R)return false;
        int r=a[h+R];Row v=tab[q][r];
        if(q==27&&r==1)v={wt,dt,qt};
        a[h+R]=v.w;h+=v.d;q=v.t;
    }
    return false;
}
int main(int argc,char**argv){
    if(argc!=2)return 2;
    ifstream f(argv[1]);string l;vector<bool>have(300);
    while(getline(f,l)){
        if(l.empty()||l[0]=='#')continue;
        stringstream s(l);int q,r,w,t;char d;s>>q>>r>>w>>d>>t;
        tab[q][r]={w,d=='R'?1:-1,t};have[q]=true;
    }
    for(int q=0;q<300;q++)if(have[q]&&q!=171)qs.push_back(q);
    int tested=0;
    for(int w:{0,1})for(int d:{-1,1})for(int q:qs){
        tested++;
        bool ok=true;
        for(int m:{0,1023,341,682})for(int sec:{0,1})if(!run(w,d,q,sec,sec?202:22,m))ok=false;
        if(!ok)continue;
        cerr<<"coarse "<<w<<' '<<d<<' '<<q<<'\n';
        for(int m=0;m<1024&&ok;m++)for(int sec:{0,1})if(!run(w,d,q,sec,sec?202:22,m))ok=false;
        if(ok)cout<<"SUCCESS "<<w<<' '<<d<<' '<<q<<'\n';
    }
    cout<<"tested "<<tested<<'\n';
}
