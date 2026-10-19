// Discovery only: head-offset merges with exact local numeric endpoint comparisons.
// Adapted from ProveIt discovery neutral_domains/helper_domains, attributed in parent archive.
#include <bits/stdc++.h>
using namespace std;
struct Row {int w,d,z;}; struct Conf {int q,h,t;};
struct Case {int input,t,h; vector<Conf> goals;};
Row tab[256][2]; bool exists_[256]; vector<int> states,invs[256];
vector<Case> pre[256],cases[2];
int L=5,R=5,W,N,F,maxnew=65,maxold=65,retained,deleted,offset;
long long contexttests=0;
inline int mapped(int q){return q==deleted?retained:q;}
bool test(int input,Row rt[2],bool complete){
 for(auto const&c:cases[input]){
  contexttests++; int x=c.t,pos=c.h,s=retained;bool yes=false;
  for(int tt=0;tt<maxnew;++tt){
   if(pos < -L || pos>R || s==254)break;
   int bb=(x>>(L+pos))&1;
   if(s==retained&&bb!=input&&!complete){yes=true;break;}
   Row a=s==retained?rt[bb]:tab[s][bb];
   if(s!=retained&&a.z==deleted){a.d+=offset;a.z=retained;}
   x=(x&~(1<<(L+pos)))|(a.w<<(L+pos));pos+=a.d;s=a.z;
   for(auto const&g:c.goals)if(s==mapped(g.q)&&pos==g.h+(g.q==deleted?offset:0)&&x==g.t){yes=true;break;}
   if(yes)break;
  }
  if(!yes)return false;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc<3)return 2;
 if(argc>3)L=stoi(argv[3]);if(argc>4)R=stoi(argv[4]);if(argc>5)maxold=stoi(argv[5]);if(argc>6)maxnew=stoi(argv[6]);
 W=L+R+1;N=1<<W;F=N-1;
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};exists_[q]=true;}
 for(int q=0;q<256;++q)if(exists_[q])states.push_back(q);
 ifstream dd(argv[2]);int q,m;while(dd>>q>>m)invs[q].push_back(m);
 for(int q:states){
  sort(invs[q].begin(),invs[q].end(),[](int a,int b){return ((a*101)&F)<((b*101)&F);});
  for(int m:invs[q]){Case c{q,m,0,{}};int h=0,t=m,s=q;
   for(int k=0;k<maxold;k++){
    if(s==254||h<-L||h>R)break;
    int b=(t>>(L+h))&1;Row a=tab[s][b];t=(t&~(1<<(L+h)))|(a.w<<(L+h));s=a.z;h+=a.d;c.goals.push_back({s,h,t});
   }
   pre[q].push_back(move(c));
  }
 }
 long long pairs=0,checked=0,candidates=0;auto start=chrono::steady_clock::now();
 for(int q:states)if(q!=95)for(int off:{-2,2}){
  bool eligible=true;for(int s:states)for(int b=0;b<2;b++)if(s!=q&&tab[s][b].z==q&&abs(tab[s][b].d+off)!=1)eligible=false;
  if(!eligible)continue;
  for(int p:states)if(p!=q){
   retained=p;deleted=q;offset=off;
   for(int b=0;b<2;b++)cases[b].clear();
   for(int s:{p,q})for(auto c:pre[s]){c.h=s==q?off:0;int b=(c.t>>(L+c.h))&1;cases[b].push_back(move(c));}
   for(int b=0;b<2;b++)stable_sort(cases[b].begin(),cases[b].end(),[](auto const&a,auto const&b){return ((a.t*101)&F)<((b.t*101)&F);});
   vector<Row>valid[2];Row rr[2];
   for(int b=0;b<2;b++)for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:states)if(z!=q){
    rr[b]={w,d,z};checked++;
    if(test(b,rr,false))valid[b].push_back(rr[b]);
   }
   for(auto a:valid[0])for(auto b:valid[1]){
    rr[0]=a;rr[1]=b;
    if(test(0,rr,true)&&test(1,rr,true)){candidates++;cout<<"OFFSET "<<off<<" FOLD "<<p<<" "<<q<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;}
   }
   if(++pairs%2000==0)cerr<<"pairs "<<pairs<<" checks "<<checked<<" candidates "<<candidates<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
  }
 }
 cerr<<"FINISHED pairs "<<pairs<<" checks "<<checked<<" candidates "<<candidates<<" contexttests "<<contexttests<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
