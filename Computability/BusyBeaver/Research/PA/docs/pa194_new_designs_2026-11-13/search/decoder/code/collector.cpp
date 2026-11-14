#define PARAMETER_SCREEN_NO_MAIN
#include "screen.cpp"
#include <cmath>
#include <random>
#include <set>
#include <sstream>
#include <unordered_set>
struct Attr{int h,l,m,mi,inc,len,bad;};
struct Node{int l,r;Attr a;};
map<int,Attr> leafattrs;
int leaf(int q){return -q-2;}int physical(int id){return -id-2;}
struct E{
 vector<Node>ns;unordered_map<uint64_t,int>ix;
 Attr at(int t)const{return t<0?leafattrs.at(physical(t)):ns[t].a;}
 int pair(int l,int r){auto k=key(l,r);auto it=ix.find(k);if(it!=ix.end())return it->second;
  Attr a=at(l),b=at(r),v;v.h=1+max(a.h,b.h);v.l=a.l+1;v.m=max({a.l+1,a.m,b.m});v.mi=max({a.mi,b.mi,a.inc?1+a.l:0});v.inc=a.inc;v.len=a.len+b.len;
  v.bad=a.bad+b.bad+((l<0&&physical(l)==194)?1:0)+((r<0&&physical(r)==69)?1:0);
  int id=ns.size();ns.push_back({l,r,v});ix[k]=id;return id;
 }
 vector<int>reachable(int root)const{vector<int>v;unordered_set<int>seen;function<void(int)>go=[&](int t){if(t<0||!seen.insert(t).second)return;v.push_back(t);go(ns[t].l);go(ns[t].r);};go(root);return v;}
 Result evaluate(int root){vector<T>ts;unordered_map<int,int>local;
  function<int(int)>go=[&](int t){auto it=local.find(t);if(it!=local.end())return it->second;T v;
   if(t<0)v={0,physical(t),-1,-1};else{auto old=ns[t];int l=go(old.l),r=go(old.r);v={1,l,r,0};}
   int j=ts.size();local[t]=j;ts.push_back(v);return j;};
  int r=go(root);return calc(ts,r,array<int,6>{});
 }
 int replace(int root,int old,int fresh){unordered_map<int,int>memo;function<int(int)>go=[&](int t){if(t<0||t==old)return t==old?fresh:t;auto it=memo.find(t);if(it!=memo.end())return it->second;auto n=ns[t];int l=go(n.l),r=go(n.r);int z=pair(l,r);memo[t]=z;return z;};return go(root);}
 int replace_one(int root,int k,int fresh){
  if(k==0)return fresh;
  auto n=ns[root];int lc=at(n.l).len-1;
  if(k<=lc)return pair(replace_one(n.l,k-1,fresh),n.r);
  return pair(n.l,replace_one(n.r,k-1-lc,fresh));
 }
 int occurrence(int root,int k){
  if(k==0)return root;
  auto n=ns[root];int lc=at(n.l).len-1;
  return k<=lc?occurrence(n.l,k-1):occurrence(n.r,k-1-lc);
 }
 int rename(int root,int head,int from,int to){static const int lo[]={18,35,54,70,86,102},hi[]={35,54,70,86,102,121};int mp[3];for(int k=0;k<3;k++)mp[perms[from][k]]=perms[to][k];
  unordered_map<int,int>memo;function<int(int)>whole=[&](int t){if(t<0){int q=physical(t);for(int k=0;k<3;k++)if(vars[k]==q)return leaf(vars[mp[k]]);return t;}auto it=memo.find(t);if(it!=memo.end())return it->second;auto n=ns[t];int l=whole(n.l),r=whole(n.r);int z=pair(l,r);memo[t]=z;return z;};
  function<int(int,int)>go=[&](int t,int p){int len=at(t).len;if(p>=hi[head]||p+len<=lo[head])return t;if(p>=lo[head]&&p+len<=hi[head])return whole(t);auto n=ns[t];int l=go(n.l,p),r=go(n.r,p+at(n.l).len);return pair(l,r);};return go(root,0);
 }
 string jsonleaf(int t)const{int q=physical(t);switch(q){case -1:return "[\"leaf\",\"breakTo\",1]";case 61:return "[\"leaf\",\"inc\",1]";case 90:return "\"node65\"";case 98:return "\"node55\"";case 12:return "\"node58\"";case 166:return "\"node70\"";case 19:return "\"node49\"";case 69:return "\"node72\"";case 213:return "\"node75\"";case 194:return "\"node142\"";case 221:return "\"node150\"";case 99:return "\"node60\"";case 190:return "\"node61\"";}throw runtime_error("unknown leaf");}
 void save(int root,string path){ofstream out(path);auto v=reachable(root);out<<"{\"root\":\"g"<<root<<"\",\"rules\":{";bool first=true;for(auto t:v){auto n=ns[t];if(!first)out<<',';first=false;auto str=[&](int c){return c<0?jsonleaf(c):"\"g"+to_string(c)+"\"";};out<<"\"g"<<t<<"\":["<<str(n.l)<<','<<str(n.r)<<']';}out<<"}}\n";}
};
struct S{int root;array<int,6>p;int score,eff,n,fold,pen;};
S scored(E&e,int root,array<int,6>p){auto v=e.evaluate(root);auto a=e.at(root);int pen=4*a.bad+4*max(a.m-6,0)+4*max(a.mi-5,0)+max(a.h-38,0);return {root,p,v.effective+pen,v.effective,v.n,v.fold,pen};}
int main(int argc,char**argv){
 if(argc<5){cerr<<"joint_anneal templates leaf_attrs output_prefix seconds [seed]\n";return 2;}
 use_compatible=true;
 ifstream in(argv[1]);int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;vector<S>pool;int nt;in>>nt;for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<int>values(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;values[i]=t.op?e.pair(values[t.a],values[t.b]):leaf(t.a);}pool.push_back(scored(e,values[rt],{}));}
 string out=argv[3];double seconds=atof(argv[4]);uint64_t seed=argc>5?strtoull(argv[5],0,10):140214;
 mt19937_64 rng(seed);auto pick=[&](int n){return int(rng()%n);};auto uniform=[&](){return generate_canonical<double,53>(rng);};
 int best=999;long long iterations=0,accepted=0,hits=0;auto start=chrono::steady_clock::now();auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 for(auto s:pool)best=min(best,s.score);cout<<"INITIAL "<<pool.size()<<" best "<<best<<" seed "<<seed<<endl;
 ofstream log(out+".csv");log<<"iteration,score,effective,nodes,folds,penalty,seconds,permutations\n";
 unordered_set<int>seen,hitseen;int cycle=0;
 while(elapsed()<seconds && hits<1000){
  sort(pool.begin(),pool.end(),[](auto a,auto b){return a.score<b.score;}); S current=pool[pick(min(60,int(pool.size())))];
  cycle++; if(false){for(int j=0;j<1+pick(3);j++){int h=pick(6),p=pick(6);current.root=e.rename(current.root,h,current.p[h],p);current.p[h]=p;}current=scored(e,current.root,current.p);}
  for(int j=0;j<4000&&elapsed()<seconds&&hits<1000;j++){
   iterations++;int nr=current.root;auto pp=current.p;
   if(false && pick(1000)<3){int h=pick(6),p=pick(6);nr=e.rename(nr,h,pp[h],p);pp[h]=p;}
   else {
    int changes=pick(100)<15?2+(pick(100)<20):1;
    for(int changes_i=0;changes_i<changes;changes_i++){
     bool local=pick(100)<65;int k=0,x;
     if(local){k=pick(e.at(nr).len-1);x=e.occurrence(nr,k);}
     else {auto reach=e.reachable(nr);x=reach[pick(reach.size())];}
     auto nn=e.ns[x];vector<int>opts;
     if(nn.l>=0){auto a=e.ns[nn.l];int r=e.pair(a.r,nn.r);opts.push_back(e.pair(a.l,r));}
     if(nn.r>=0){auto a=e.ns[nn.r];int l=e.pair(nn.l,a.l);opts.push_back(e.pair(l,a.r));}
     if(opts.empty())continue;
     int fresh=opts[pick(opts.size())];nr=local?e.replace_one(nr,k,fresh):e.replace(nr,x,fresh);
    }
   }
   S ns=scored(e,nr,pp);double temp=.04+.38*(1.-j/4000.);
   if(ns.score<=current.score||uniform()<exp((current.score-ns.score)/temp)){
    current=ns;accepted++;
    if(ns.score<best){best=ns.score;e.save(ns.root,out+".best.grammar.json");cout<<"BEST score "<<best<<" eff "<<ns.eff<<" nodes "<<ns.n<<" folds "<<ns.fold<<" pen "<<ns.pen<<" iteration "<<iterations<<" seconds "<<elapsed()<<endl;}
    if(ns.score<=62&&!ns.pen&&seen.insert(ns.root).second){pool.push_back(ns);if(pool.size()>250){sort(pool.begin(),pool.end(),[](auto a,auto b){return a.score<b.score;});pool.resize(200);}}
    if(ns.eff<=60&&!ns.pen&&hits<1000&&hitseen.insert(ns.root).second){
     string path=out+".hit"+to_string(hits)+".grammar.json";e.save(ns.root,path);log<<iterations<<','<<ns.score<<','<<ns.eff<<','<<ns.n<<','<<ns.fold<<','<<ns.pen<<','<<elapsed()<<',';for(int p:ns.p)log<<p;log<<'\n';log.flush();
     cout<<"HIT "<<hits<<" score "<<ns.score<<" nodes "<<ns.n<<" folds "<<ns.fold<<" seconds "<<elapsed()<<endl;hits++;
    }
   }
   if(iterations%50000==0){
    E clean;unordered_map<int,int>mem;function<int(int)>copy=[&](int t){if(t<0)return t;auto it=mem.find(t);if(it!=mem.end())return it->second;auto n=e.ns[t];int l=copy(n.l),r=copy(n.r);int z=clean.pair(l,r);mem[t]=z;return z;};
    for(auto &s:pool)s.root=copy(s.root);current.root=copy(current.root);e=move(clean);seen.clear();for(auto s:pool)seen.insert(s.root);
   }
  }
  cout<<"CYCLE "<<cycle<<" best "<<best<<" now "<<current.score<<" pool "<<pool.size()<<" iterations "<<iterations<<" nodes "<<e.ns.size()<<" seconds "<<elapsed()<<endl;
 }
 sort(pool.begin(),pool.end(),[](auto a,auto b){return a.score<b.score;});
 for(int j=0;j<min(60,int(pool.size()));j++)e.save(pool[j].root,out+".seed"+to_string(j)+".grammar.json");
 cout<<"DONE iterations "<<iterations<<" accepted "<<accepted<<" hits "<<hits<<" best "<<best<<" seconds "<<elapsed()<<endl;
}
