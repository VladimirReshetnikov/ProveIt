// Head-offset state identification, finite candidate discovery only.
// Adapted from the supplied neutral/helper window-domain search structure.
#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,z;};struct Conf{int q,h,t;};
struct Case{int input,t;vector<Conf>goals;};
Row tab[256][2];bool ex[256];vector<int>states,invs[256];
vector<Case>pre[256];vector<const Case*>cases[2];
int L=5,R=5,W,N,F,maxold=65,maxnew=65,keep_,drop_,shift_;
long long tests_=0;
int mp(int q){return q==drop_?keep_:q;}
int off(int q){return q==drop_?-2*shift_:0;}
int tagged(int q,int h,int t){return q==drop_?t^(1<<(L+h-shift_)):t;}
Row change(Row a){if(a.z==drop_){a.w^=1;a.d=-a.d;a.z=keep_;}return a;}
bool check(int input,Row rr[2],bool full){
 for(auto ptr:cases[input]){
  auto &c=*ptr;tests_++;int t=tagged(c.input,0,c.t),h=off(c.input),s=keep_;bool ok=false;
  for(int k=0;k<maxnew;k++){
   if(h < -L||h>R||s==254)break;
   int b=(t>>(L+h))&1;
   if(s==keep_&&b!=input&&!full){ok=true;break;}
   Row a=s==keep_?rr[b]:change(tab[s][b]);
   if(abs(a.d)!=1)break;
   t=(t&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;s=a.z;
   for(auto &g:c.goals)if((g.q!=drop_||(g.h-shift_>=-L&&g.h-shift_<=R))&&s==mp(g.q)&&h==g.h+off(g.q)&&t==tagged(g.q,g.h,g.t)){ok=true;break;}
   if(ok)break;
  }
  if(!ok)return false;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc<3)return 2;
 if(argc>3)L=R=stoi(argv[3]);if(argc>4)maxold=maxnew=stoi(argv[4]);
 W=L+R+1;N=1<<W;F=N-1;
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};ex[q]=true;}
 for(int q=0;q<256;q++)if(ex[q])states.push_back(q);
 ifstream dom(argv[2]);int q,m;while(dom>>q>>m)invs[q].push_back(m);
 for(int q:states){
  sort(invs[q].begin(),invs[q].end(),[](int a,int b){return ((a*101)&F)<((b*101)&F);});
  for(int m:invs[q]){Case c{q,m,{}};int h=0,t=m,s=q;
   for(int k=0;k<maxold;k++){
    if(s==254||h<-L||h>R)break;
    int b=(t>>(L+h))&1;Row a=tab[s][b];t=(t&~(1<<(L+h)))|(a.w<<(L+h));h+=a.d;s=a.z;c.goals.push_back({s,h,t});
   }
   pre[q].push_back(move(c));
  }
 }
 long long pairs=0,checked=0,found=0;auto start=chrono::steady_clock::now();
 for(int drop:states)if(drop!=95)for(int sh:{-1,1})for(int keep:states)if(keep!=drop){
   keep_=keep;drop_=drop;shift_=sh;
   bool feasible=true;
   for(int p:states)if(p!=keep&&p!=drop)for(int b=0;b<2;b++)if(tab[p][b].z==drop&&tab[p][b].d!=sh)feasible=false;
   if(!feasible)continue;
   for(auto&v:cases)v.clear();
   for(int q:{keep,drop})for(auto &c:pre[q])cases[(c.t>>(L+off(q)))&1].push_back(&c);
   for(auto&v:cases)stable_sort(v.begin(),v.end(),[](const Case*a,const Case*b){return ((a->t*101)&F)<((b->t*101)&F);});
   vector<Row> opts[2];Row rr[2];
   for(int b=0;b<2;b++)for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:states)if(z!=drop){
    rr[b]={w,d,z};checked++;if(check(b,rr,false))opts[b].push_back(rr[b]);
   }
   for(auto a:opts[0])for(auto b:opts[1]){
    rr[0]=a;rr[1]=b;if(check(0,rr,true)&&check(1,rr,true)){
     cout<<"OFFSET_TAG "<<keep<<" "<<drop<<" "<<sh<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;found++;
    }
   }
   if(++pairs%2000==0)cerr<<"pairs "<<pairs<<" checked "<<checked<<" found "<<found<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"DONE pairs "<<pairs<<" checked "<<checked<<" tests "<<tests_<<" found "<<found<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
