#include <bits/stdc++.h>
using namespace std;
struct Row {int w,d,z; bool operator==(Row const&o)const{return w==o.w&&d==o.d&&z==o.z;}};
Row tab[256][2]; bool exists[256];vector<int> states, invs[256];
#ifndef RADIUS
#define RADIUS 4
#endif
constexpr int R=RADIUS,W=2*R+1,N=1<<W,F=N-1;
int maxdur=21;
struct Case {int tape,want,h,target;};
vector<Case> cases[2];int retained,deleted;
inline int mapped(int q){return q==deleted?retained:q;}
bool test(int input,Row rt[2],bool complete){
 for(Case c:cases[input]){
   int x=c.tape,pos=0,s=retained;bool yes=false;
   for(int tt=0;tt<maxdur;++tt){
     if(pos < -R||pos>R||s==254)return false;
     int bb=(x>>(R+pos))&1;
     if(s==retained&&bb!=input&&!complete){yes=true;break;}
     Row t=s==retained?rt[bb]:tab[s][bb];
     x=(x&~(1<<(R+pos)))|(t.w<<(R+pos));pos+=t.d;s=mapped(t.z);
     if(s==c.target&&pos==c.h&&x==c.want){yes=true;break;}
   }
   if(!yes)return false;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc<3){cerr<<"Usage: coupled MAX_STEPS TABLE\n";return 2;}
 maxdur=stoi(argv[1]);
 ifstream f(argv[2]);if(!f){cerr<<"Cannot read table\n";return 2;}string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};exists[q]=true;}
 for(int q=0;q<256;++q)if(exists[q])states.push_back(q);
 static bool seen[256][N];queue<pair<int,int>>todo;
 for(int m=0;m<N;++m){seen[95][m]=true;todo.push({95,m});}
 while(!todo.empty()){
  auto[q,m]=todo.front();todo.pop();invs[q].push_back(m);if(q==254)continue;
  Row t=tab[q][(m>>R)&1];int x=(m&~(1<<R))|(t.w<<R);int ys[2];
  if(t.d==1){ys[0]=x>>1;ys[1]=ys[0]|(1<<(W-1));}else{ys[0]=(x<<1)&F;ys[1]=ys[0]|1;}
  for(int y:ys)if(!seen[t.z][y]){seen[t.z][y]=true;todo.push({t.z,y});}
 }
 cerr<<"Searching coupled rows R="<<R<<" maxdur="<<maxdur<<endl;
 long long paircount=0,checked=0,candidate=0,partials=0;
 for(int p:states)for(int q:states)if(p<q){
   retained=p;deleted=q;
   for(int b=0;b<2;++b){cases[b].clear();
    for(int s:{p,q})for(int m:invs[s])if(((m>>R)&1)==b){
      Row goal=tab[s][b];cases[b].push_back({m,(m&~(1<<R))|(goal.w<<R),goal.d,mapped(goal.z)});
    }
    // Deterministic scrambling places various head-neighborhood values early.
    stable_sort(cases[b].begin(),cases[b].end(),[](auto a,auto b){return ((a.tape*101)&F)<((b.tape*101)&F);});
   }
   vector<Row> ok[2];Row rows[2];
   for(int b=0;b<2;++b){
    for(int w=0;w<2;++w)for(int d:{-1,1})for(int z:states)if(z!=deleted){
     rows[b]={w,d,z};if(test(b,rows,false))ok[b].push_back(rows[b]);checked++;
    }
    if(ok[b].empty())break;
   }
   partials+=ok[0].size()+ok[1].size();
   for(auto r0:ok[0])for(auto r1:ok[1]){rows[0]=r0;rows[1]=r1;
    if(test(0,rows,true)&&test(1,rows,true)){
     cout<<p<<" "<<q<<" "<<r0.w<<" "<<r0.d<<" "<<r0.z<<" "<<r1.w<<" "<<r1.d<<" "<<r1.z<<endl;candidate++;
    }
   }
   if(++paircount%5000==0)cerr<<"pairs "<<paircount<<" checked "<<checked<<" partials "<<partials<<" found "<<candidate<<endl;
 }
 cerr<<"FINISHED pairs "<<paircount<<" checked "<<checked<<" partials "<<partials<<" candidates "<<candidate<<endl;
}
