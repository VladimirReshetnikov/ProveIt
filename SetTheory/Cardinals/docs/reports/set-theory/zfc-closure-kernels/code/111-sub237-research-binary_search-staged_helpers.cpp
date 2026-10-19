#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,z;};struct Conf{int q,h,t;};
Row tab[256][2];bool exists_[256];vector<int> states,invs[256];
int L=4,R=4,W,N,F,maxnew=33,maxold=33;
struct Case{int input,t;vector<Conf> goals;};vector<Case> cases[2];
int retained,deleted;long long contexttests=0;int passed_cases=0;
inline int mapped(int q){return q==deleted?retained:q;}

struct Patch{int q,b;Row a;};vector<Patch>patches;vector<int>byedge[512];
vector<int>failededges;
bool testcases(vector<Case>const&cs,int entry,int input,Row rt[2],bool complete,int pi=-1,bool savefail=false,int pj=-1){
 passed_cases=0;for(auto const&c:cs){
  contexttests++;int x=c.t,pos=0,s=entry;bool yes=false;vector<int>used;
  for(int tt=0;tt<maxnew;++tt){
   if(pos < -L||pos>R||s==254)break;
   int bb=(x>>(L+pos))&1;
   if(s==retained&&bb!=input&&!complete){yes=true;break;}
   Row a;
   if(s==retained)a=rt[bb];
   else {if(savefail)used.push_back(2*s+bb);a=pi>=0&&patches[pi].q==s&&patches[pi].b==bb?patches[pi].a:(pj>=0&&patches[pj].q==s&&patches[pj].b==bb?patches[pj].a:tab[s][bb]);}
   x=(x&~(1<<(L+pos)))|(a.w<<(L+pos));pos+=a.d;s=mapped(a.z);
   for(auto const&g:c.goals)if(s==mapped(g.q)&&pos==g.h&&x==g.t){yes=true;break;}
   if(yes)break;
  }
  if(yes)passed_cases++;if(!yes){if(savefail){sort(used.begin(),used.end());used.erase(unique(used.begin(),used.end()),used.end());failededges=move(used);}return false;}
 }
 return true;
}
bool test(int b,Row rt[2],bool complete,int pi=-1,bool savefail=false,int pj=-1){return testcases(cases[b],retained,b,rt,complete,pi,savefail,pj);}
int main(int argc,char**argv){
 if(argc<2)return 2;
 if(argc>2)L=stoi(argv[2]);if(argc>3)R=stoi(argv[3]);if(argc>4)maxold=stoi(argv[4]);if(argc>5)maxnew=stoi(argv[5]);
 W=L+R+1;N=1<<W;F=N-1;
 ifstream f(argv[1]);string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;stringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;tab[q][b]={w,d=='R'?1:-1,z};exists_[q]=true;}
 for(int q=0;q<256;++q)if(exists_[q])states.push_back(q);
 vector<vector<bool>>seen(256,vector<bool>(N));queue<pair<int,int>>todo;
 for(int m=0;m<N;++m){seen[95][m]=true;todo.push({95,m});}
 while(!todo.empty()){
  auto[q,m]=todo.front();todo.pop();invs[q].push_back(m);if(q==254)continue;
  Row a=tab[q][(m>>L)&1];int x=(m&~(1<<L))|(a.w<<L);int ys[2];
  if(a.d==1){ys[0]=x>>1;ys[1]=ys[0]|(1<<(W-1));}else{ys[0]=(x<<1)&F;ys[1]=ys[0]|1;}
  for(int y:ys)if(!seen[a.z][y]){seen[a.z][y]=true;todo.push({a.z,y});}
 }
 if(argc>7){for(auto &v:invs)v.clear();ifstream dd(argv[7]);int q,m;while(dd>>q>>m)invs[q].push_back(m);}
 vector<Case>pre[256][2];long long contexts=0;
 for(int q:states){
  sort(invs[q].begin(),invs[q].end(),[](int a,int b){return ((a*101)&F)<((b*101)&F);});
  for(int m:invs[q]){int b=(m>>L)&1;Case c{q,m,{}};int h=0,t=m,s=q;
   for(int k=0;k<maxold;k++){
    if(s==254||h<-L||h>R)break;
    int bit=(t>>(L+h))&1;Row a=tab[s][bit];t=(t&~(1<<(L+h)))|(a.w<<(L+h));s=a.z;h+=a.d;c.goals.push_back({s,h,t});
   }
   pre[q][b].push_back(move(c));contexts++;
  }
 }
 cerr<<"Searching L="<<L<<" R="<<R<<" maxold="<<maxold<<" maxnew="<<maxnew<<" contexts="<<contexts<<endl;
 long long paircount=0,checked=0,candidate=0,partials=0;auto start=chrono::steady_clock::now();

 if(argc<7){cerr<<"Need patches file"<<endl;return 2;}
 ifstream patchesfile(argv[6]);int pq,pb,pw,pd,pz,plen;
 while(patchesfile>>pq>>pb>>pw>>pd>>pz>>plen){int id=patches.size();patches.push_back({pq,pb,{pw,pd,pz}});byedge[2*pq+pb].push_back(id);}
 cerr<<"Neutral helper patches "<<patches.size()<<endl;
 long long helpchecked=0,two_checked=0;int threshold=argc>8?stoi(argv[8]):1;
 for(int p:states)for(int q:states)if(p<q){
  bool similar=false;
  for(int b=0;b<2;b++)if(tab[p][b].w==tab[q][b].w&&tab[p][b].d==tab[q][b].d&&tab[p][b].z==tab[q][b].z)similar=true;
  if(!similar)continue;
  retained=p;deleted=q;
  for(int b=0;b<2;++b){cases[b].clear();for(int s:{p,q})cases[b].insert(cases[b].end(),pre[s][b].begin(),pre[s][b].end());
   stable_sort(cases[b].begin(),cases[b].end(),[](auto const&a,auto const&b){return ((a.t*101)&F)<((b.t*101)&F);});
  }
  vector<Row>baseok[2];Row rows[2];map<int,array<vector<Row>,2>> repairs;map<pair<int,int>,array<vector<Row>,2>> tworepairs;
  for(int b=0;b<2;++b){
   for(int w=0;w<2;++w)for(int d:{-1,1})for(int z:states)if(z!=deleted){
    rows[b]={w,d,z};checked++;
    if(test(b,rows,false,-1,true)){baseok[b].push_back(rows[b]);continue;}
    vector<int>options;
    for(int e:failededges)for(int pi:byedge[e])if(patches[pi].q!=p&&patches[pi].q!=q)options.push_back(pi);
    sort(options.begin(),options.end());options.erase(unique(options.begin(),options.end()),options.end());
    for(int pi:options){
     helpchecked++;
     if(test(b,rows,false,pi,true)) {repairs[pi][b].push_back(rows[b]);continue;}
     if(passed_cases<threshold)continue;
     vector<int>seconds;
     for(int e:failededges)for(int pj:byedge[e])if(patches[pj].q!=p&&patches[pj].q!=q)seconds.push_back(pj);
     sort(seconds.begin(),seconds.end());seconds.erase(unique(seconds.begin(),seconds.end()),seconds.end());
     for(int pj:seconds){
      if(pi==pj||(patches[pi].q==patches[pj].q&&patches[pi].b==patches[pj].b))continue;
      two_checked++;
      if(test(b,rows,false,pi,false,pj))tworepairs[minmax(pi,pj)][b].push_back(rows[b]);
     }
    }
   }
  }
  // A patch can also repair a conflict that appears only after both rows are filled.
  for(Row a:baseok[0])for(Row b:baseok[1]){
   rows[0]=a;rows[1]=b;
   if(test(0,rows,true,-1,true)&&test(1,rows,true,-1,true)){
    cout<<"BASE "<<p<<" "<<q<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;candidate++;
   }else for(int e:failededges)for(int pi:byedge[e])if(patches[pi].q!=p&&patches[pi].q!=q)repairs[pi];
  }
  for(auto &[pi,rr]:repairs){
   vector<Row>ok[2];
   for(int b=0;b<2;b++){
    ok[b]=rr[b];
    for(auto a:baseok[b]){rows[b]=a;helpchecked++;if(test(b,rows,false,pi))ok[b].push_back(a);}
   }
   for(auto a:ok[0])for(auto b:ok[1]){
    rows[0]=a;rows[1]=b;helpchecked++;
    if(!test(0,rows,true,pi)||!test(1,rows,true,pi))continue;
    Patch helper=patches[pi];
    if(!testcases(pre[helper.q][helper.b],helper.q,helper.b,rows,true,pi))continue;
    cout<<"HELPER "<<helper.q<<" "<<helper.b<<" "<<helper.a.w<<" "<<helper.a.d<<" "<<helper.a.z<<" FOLD "<<p<<" "<<q<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;candidate++;
   }
  }
  for(auto const&kv:repairs)for(auto const&kv2:repairs)if(kv.first<kv2.first)tworepairs[{kv.first,kv2.first}];
  for(auto &[key,rr]:tworepairs){
   auto[pi,pj]=key;Patch h0=patches[pi],h1=patches[pj];
   if(h0.q==h1.q&&h0.b==h1.b)continue;
   vector<Row>ok[2];
   for(int b=0;b<2;b++){
    ok[b]=rr[b];vector<Row>other=baseok[b];
    for(int k:{pi,pj})if(repairs.count(k))for(auto a:repairs[k][b])other.push_back(a);
    for(auto a:other){rows[b]=a;two_checked++;if(test(b,rows,false,pi,false,pj))ok[b].push_back(a);}
    sort(ok[b].begin(),ok[b].end(),[](auto a,auto b){return tie(a.w,a.d,a.z)<tie(b.w,b.d,b.z);});
    ok[b].erase(unique(ok[b].begin(),ok[b].end(),[](auto a,auto b){return tie(a.w,a.d,a.z)==tie(b.w,b.d,b.z);}),ok[b].end());
   }
   for(auto a:ok[0])for(auto b:ok[1]){
    rows[0]=a;rows[1]=b;two_checked++;
    if(!test(0,rows,true,pi,false,pj)||!test(1,rows,true,pi,false,pj))continue;
    if(!testcases(pre[h0.q][h0.b],h0.q,h0.b,rows,true,pi,false,pj))continue;
    if(!testcases(pre[h1.q][h1.b],h1.q,h1.b,rows,true,pi,false,pj))continue;
    cout<<"TWOHELPER "<<h0.q<<" "<<h0.b<<" "<<h0.a.w<<" "<<h0.a.d<<" "<<h0.a.z<<" "<<h1.q<<" "<<h1.b<<" "<<h1.a.w<<" "<<h1.a.d<<" "<<h1.a.z<<" FOLD "<<p<<" "<<q<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;candidate++;
   }
  }
  if(++paircount%10==0)cerr<<"pairs "<<paircount<<" checked "<<checked<<" helperchecks "<<helpchecked<<" twohelperchecks "<<two_checked<<" found "<<candidate<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"FINISHED pairs "<<paircount<<" checked "<<checked<<" helperchecks "<<helpchecked<<" twohelperchecks "<<two_checked<<" candidates "<<candidate<<" contexttests "<<contexttests<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
