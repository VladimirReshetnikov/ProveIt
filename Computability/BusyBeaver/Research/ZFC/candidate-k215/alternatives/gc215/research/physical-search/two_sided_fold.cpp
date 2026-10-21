// Search positive two-sided joins, with each modified branch synthesized alone.
// A hit needs independent reconstruction and proof. A miss is only a bounded
// result for the supplied finite inductive invariant.
#include <iostream>
#include <vector>
#include <fstream>
#include <algorithm>
#include <chrono>
using namespace std;
struct Tr{int w,d,t;};
struct Config{int q,h,tape;};
struct Case{int origin,mask;vector<Config> old;};
Tr T[1000][2];vector<int> masks[1000],states;int R,Start,Cap;
vector<Config> trace(int q,int tape){
  int h=0;vector<Config>a;
  for(int k=0;k<Cap;k++){
    int j=h+R;if(j<0||j>2*R||q==254)break;
    auto tr=T[q][(tape>>j)&1];
    tape=(tape&~(1<<j))|(tr.w<<j);h+=tr.d;q=tr.t;
    a.push_back({q,h,tape});
  }return a;
}
bool test(int p,int q,const Case&c,Tr patch){
  int tape=c.mask,h=0,z=p;
  for(int step=0;step<Cap;step++){
    int j=h+R;if(j<0||j>2*R||z==254)return false;
    if(step>0&&z==p)return false;
    auto a=step==0?patch:T[z][(tape>>j)&1];
    tape=(tape&~(1<<j))|(a.w<<j);h+=a.d;z=a.t==q?p:a.t;
    for(auto goal:c.old)if(z==(goal.q==q?p:goal.q)&&h==goal.h&&tape==goal.tape)return true;
  }return false;
}
int main(int argc,char**argv){
  ifstream f(argv[1]);int ns;f>>R>>Start>>ns;Cap=argc>2?stoi(argv[2]):32;
  for(int i=0;i<ns;i++){
    int q,n;f>>q;states.push_back(q);
    for(int b=0;b<2;b++)f>>T[q][b].w>>T[q][b].d>>T[q][b].t;
    f>>n;for(int j=0;j<n;j++){int m;f>>m;masks[q].push_back(m);}
  }
  vector<Case> cases[1000][2];
  for(int q:states)for(int m:masks[q])cases[q][(m>>R)&1].push_back({q,m,trace(q,m)});
  unsigned long long attempts=0;int both=0,one=0;
  auto started=chrono::steady_clock::now();
  for(int ip=0;ip<ns;ip++)for(int iq=ip+1;iq<ns;iq++){
    int p=states[ip],q=states[iq];if(q==Start)continue;
    vector<Tr> valid[2];
    for(int b=0;b<2;b++){
      vector<const Case*> tests;auto &pc=cases[p][b],&qc=cases[q][b];
      for(int i=0;i<(int)max(pc.size(),qc.size());i++){
        if(i<(int)pc.size())tests.push_back(&pc[i]);
        if(i<(int)qc.size())tests.push_back(&qc[i]);
      }
      for(int t:states)if(t!=q)for(int w=0;w<2;w++)for(int d:{-1,1}){
        Tr patch{w,d,t};attempts++;bool ok=true;
        for(auto c:tests)if(!test(p,q,*c,patch)){ok=false;break;}
        if(ok)valid[b].push_back(patch);
      }
      if(valid[b].empty())break;
    }
    if(!valid[0].empty())one++;
    if(!valid[0].empty()&&!valid[1].empty()){
      both++;cout<<"HIT "<<p<<" "<<q<<"\n";
      for(int b=0;b<2;b++)for(auto a:valid[b])cout<<b<<" "<<a.w<<" "<<a.d<<" "<<a.t<<"\n";
      cout.flush();
    }
  }
  double secs=chrono::duration<double>(chrono::steady_clock::now()-started).count();
  cout<<"END radius "<<R<<" cap "<<Cap<<" attempts "<<attempts<<" one "<<one<<" both "<<both<<" seconds "<<secs<<"\n";
}
