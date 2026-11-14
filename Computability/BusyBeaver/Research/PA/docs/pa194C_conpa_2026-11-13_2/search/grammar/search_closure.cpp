#define PARAMETER_SCREEN_NO_MAIN
#include "screen_closure.cpp"
#include <cmath>
#include <random>
#include <set>
#include <sstream>
#include <unordered_set>
struct Attr{int h,l,m,mi,inc,len,bad;};
struct Node{int l,r;Attr a;};
map<int,Attr> leafattrs;
int leaf(int q){return -q-2;}int physical(int id){return -id-2;}
int leaf_physical(int t){switch(physical(t)){case 3000:return 28;case 3001:return 43;case 3002:return 58;case 3003:return 59;case 3004:return 30;case 3005:return 31;case 3006:return 130;case 3007:return 107;case 3008:return 72;case 3009:return 125;case 3010:return 61;case 3011:return 69;case 3012:return 123;case 3013:return 124;case 3014:return 194;case 3015:return 128;case 3016:return 194;case 3017:return 196;case 3018:return 109;case 3019:return 130;case 3020:return -1;}throw runtime_error("unknown source token");}
struct E{
 vector<Node>ns;unordered_map<uint64_t,int>ix;
 Attr at(int t)const{return t<0?leafattrs.at(physical(t)):ns[t].a;}
 int pair(int l,int r){auto k=key(l,r);auto it=ix.find(k);if(it!=ix.end())return it->second;
  Attr a=at(l),b=at(r),v;v.h=1+max(a.h,b.h);v.l=a.l+1;v.m=max({a.l+1,a.m,b.m});v.mi=max({a.mi,b.mi,a.inc?1+a.l:0});v.inc=a.inc;v.len=a.len+b.len;
  v.bad=a.bad+b.bad+((l<0&&physical(l)==3016)?1:0)+((r<0&&physical(r)==3011)?1:0);
  int id=ns.size();ns.push_back({l,r,v});ix[k]=id;return id;
 }
 vector<int>reachable(int root)const{vector<int>v;unordered_set<int>seen;function<void(int)>go=[&](int t){if(t<0||!seen.insert(t).second)return;v.push_back(t);go(ns[t].l);go(ns[t].r);};go(root);return v;}
 Result evaluate(int root){vector<T>ts;unordered_map<int,int>local;
  function<int(int)>go=[&](int t){auto it=local.find(t);if(it!=local.end())return it->second;T v;
   if(t<0)v={0,leaf_physical(t),-1,-1};else{auto old=ns[t];int l=go(old.l),r=go(old.r);v={1,l,r,0};}
   int j=ts.size();local[t]=j;ts.push_back(v);return j;};
  int r=go(root);return calc(ts,r,array<int,6>{});
 }
 int replace(int root,int old,int fresh){unordered_map<int,int>memo;function<int(int)>go=[&](int t){if(t<0||t==old)return t==old?fresh:t;auto it=memo.find(t);if(it!=memo.end())return it->second;auto n=ns[t];int l=go(n.l),r=go(n.r);int z=pair(l,r);memo[t]=z;return z;};return go(root);}
 int replace_occurrence(int root,int old,int fresh,mt19937_64 &rng){
  if(root<0||root==old)return root==old?fresh:root;
  unordered_map<int,bool> has;function<bool(int)>contains=[&](int t){if(t<0)return false;if(t==old)return true;auto it=has.find(t);if(it!=has.end())return it->second;auto n=ns[t];return has[t]=contains(n.l)||contains(n.r);};
  function<int(int)>go=[&](int t){if(t==old)return fresh;auto n=ns[t];bool l=contains(n.l),r=contains(n.r);if(l&&r){if(rng()%2)l=false;else r=false;}return pair(l?go(n.l):n.l,r?go(n.r):n.r);};
  return contains(root)?go(root):root;
 }
 string jsonleaf(int t)const{int q=physical(t);switch(q){case 3000:return "\"node37\"";case 3001:return "\"node39\"";case 3002:return "\"node46\"";case 3003:return "\"node16\"";case 3004:return "\"node56\"";case 3005:return "\"node19\"";case 3006:return "\"node51\"";case 3007:return "\"node53\"";case 3008:return "\"node14\"";case 3009:return "\"node63\"";case 3010:return "[\"leaf\",\"inc\",1]";case 3011:return "\"node72\"";case 3012:return "\"node29\"";case 3013:return "\"node31\"";case 3014:return "\"node68\"";case 3015:return "\"node34\"";case 3016:return "\"node142\"";case 3017:return "\"node146\"";case 3018:return "\"node10\"";case 3019:return "\"node147\"";case 3020:return "[\"leaf\",\"breakTo\",1]";}throw runtime_error("unknown leaf");}
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
 unordered_set<int>seen;int cycle=0;
 while(elapsed()<seconds){
  sort(pool.begin(),pool.end(),[](auto a,auto b){return a.score<b.score;}); S current=pool[pick(min(30,int(pool.size())))];
  cycle++;
  for(int j=0;j<4000&&elapsed()<seconds;j++){
   iterations++;int nr=current.root;auto pp=current.p;
   {auto reach=e.reachable(nr);int x=reach[pick(reach.size())];auto nn=e.ns[x];vector<int>opts;
    if(nn.l>=0){auto a=e.ns[nn.l];int r=e.pair(a.r,nn.r);opts.push_back(e.pair(a.l,r));}
    if(nn.r>=0){auto a=e.ns[nn.r];int l=e.pair(nn.l,a.l);opts.push_back(e.pair(l,a.r));}
    if(opts.empty())continue;int repl=opts[pick(opts.size())];nr=pick(4)?e.replace(nr,x,repl):e.replace_occurrence(nr,x,repl,rng);}
   S ns=scored(e,nr,pp);double temp=.015+.22*(1.-j/4000.);
   if(ns.score<=current.score||uniform()<exp((current.score-ns.score)/temp)){
    current=ns;accepted++;
    if(ns.score<best){best=ns.score;e.save(ns.root,out+".best.grammar.json");cout<<"BEST score "<<best<<" eff "<<ns.eff<<" nodes "<<ns.n<<" folds "<<ns.fold<<" pen "<<ns.pen<<" iteration "<<iterations<<" seconds "<<elapsed()<<endl;if(ns.score<60)return 0;}
    if(ns.score<=62&&!ns.pen&&seen.insert(ns.root).second){pool.push_back(ns);if(pool.size()>250){sort(pool.begin(),pool.end(),[](auto a,auto b){return a.score<b.score;});pool.resize(200);}}
    if(ns.eff<=59&&!ns.pen&&hits<200){
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
 for(int j=0;j<min(30,int(pool.size()));j++)e.save(pool[j].root,out+".seed"+to_string(j)+".grammar.json");
 cout<<"DONE iterations "<<iterations<<" accepted "<<accepted<<" hits "<<hits<<" best "<<best<<" seconds "<<elapsed()<<endl;
}
