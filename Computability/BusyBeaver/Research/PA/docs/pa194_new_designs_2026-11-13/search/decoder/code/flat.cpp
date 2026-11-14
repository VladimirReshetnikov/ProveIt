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

#include <deque>
int main(int argc,char**argv){
 if(argc<6){cerr<<"flat templates leaf_attrs prefix limit seconds\n";return 2;}
 use_compatible=true;ifstream in(argv[1]);int nb;in>>nb;
 for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;deque<int>queue;unordered_set<int>seen;int nt;in>>nt;
 for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<int>values(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;values[i]=t.op?e.pair(values[t.a],values[t.b]):leaf(t.a);}queue.push_back(values[rt]);seen.insert(values[rt]);}
 string out=argv[3];int limit=atoi(argv[4]);double seconds=atof(argv[5]);auto start=chrono::steady_clock::now();auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 long long evals=0;int expanded=0,best=60;
 while(!queue.empty()&&expanded<limit&&elapsed()<seconds){int root=queue.front();queue.pop_front();expanded++;
  unordered_set<int>neighbors;
  auto rotate=[&](int x,auto callback){auto nn=e.ns[x];if(nn.l>=0){auto a=e.ns[nn.l];int r=e.pair(a.r,nn.r);callback(e.pair(a.l,r));}if(nn.r>=0){auto a=e.ns[nn.r];int l=e.pair(nn.l,a.l);callback(e.pair(l,a.r));}};
  for(auto x:e.reachable(root))rotate(x,[&](int fresh){neighbors.insert(e.replace(root,x,fresh));});
  for(int k=0;k<e.at(root).len-1;k++){auto x=e.occurrence(root,k);rotate(x,[&](int fresh){neighbors.insert(e.replace_one(root,k,fresh));});}
  for(auto nr:neighbors){if(seen.count(nr))continue;auto ns=scored(e,nr,{});evals++;if(ns.score<best){best=ns.score;cout<<"BEST "<<best<<" raw "<<ns.n<<" folds "<<ns.fold<<" expanded "<<expanded<<" seconds "<<elapsed()<<endl;e.save(nr,out+".best.grammar.json");}if(ns.score<=60){seen.insert(nr);queue.push_back(nr);}}
  if(expanded%100==0)cout<<"EXPANDED "<<expanded<<" queue "<<queue.size()<<" seen "<<seen.size()<<" evals "<<evals<<" nodes "<<e.ns.size()<<" seconds "<<elapsed()<<endl;
  if(best<60)break;
 }
 cout<<"DONE expanded "<<expanded<<" queue "<<queue.size()<<" seen "<<seen.size()<<" evals "<<evals<<" best "<<best<<" seconds "<<elapsed()<<endl;
}
