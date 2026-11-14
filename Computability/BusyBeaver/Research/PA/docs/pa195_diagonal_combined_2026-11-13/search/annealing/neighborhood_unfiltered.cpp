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
 int rename(int root,int head,int from,int to,array<int,6> ord){static const int lens[]={17,19,16,16,16,19};int lo[6],hi[6],pos=18;for(int h:ord){lo[h]=pos;pos+=lens[h];hi[h]=pos;}int mp[3];for(int k=0;k<3;k++)mp[perms[from][k]]=perms[to][k];
  unordered_map<int,int>memo;function<int(int)>whole=[&](int t){if(t<0){int q=physical(t);for(int k=0;k<3;k++)if(vars[k]==q)return leaf(vars[mp[k]]);return t;}auto it=memo.find(t);if(it!=memo.end())return it->second;auto n=ns[t];int l=whole(n.l),r=whole(n.r);int z=pair(l,r);memo[t]=z;return z;};
  function<int(int,int)>go=[&](int t,int p){int len=at(t).len;if(p>=hi[head]||p+len<=lo[head])return t;if(p>=lo[head]&&p+len<=hi[head])return whole(t);auto n=ns[t];int l=go(n.l,p),r=go(n.r,p+at(n.l).len);return pair(l,r);};return go(root,0);
 }
 int swap_heads(int root,array<int,6> ord,int a,int b){
  vector<int>ww;function<void(int)>flat=[&](int t){if(t<0){ww.push_back(t);return;}auto n=ns[t];flat(n.l);flat(n.r);};flat(root);
  if(ww.size()!=190&&ww.size()!=191)throw runtime_error("wrong expanded word length");
  static const int lens[]={17,19,16,16,16,19};vector<vector<int>>heads(6);int pos=18;
  for(int h:ord){heads[h]=vector<int>(ww.begin()+pos,ww.begin()+pos+lens[h]);pos+=lens[h];}
  swap(ord[a],ord[b]);vector<int>fresh(ww.begin(),ww.begin()+18);for(int h:ord)fresh.insert(fresh.end(),heads[h].begin(),heads[h].end());fresh.insert(fresh.end(),ww.begin()+121,ww.end());
  pos=0;function<int(int)>fill=[&](int t){if(t<0)return fresh[pos++];auto n=ns[t];int l=fill(n.l),r=fill(n.r);return pair(l,r);};return fill(root);
 }
 string jsonleaf(int t)const{int q=physical(t);switch(q){case -1:return "[\"leaf\",\"breakTo\",1]";case 61:return "[\"leaf\",\"inc\",1]";case 90:return "\"node65\"";case 98:return "\"node55\"";case 12:return "\"node58\"";case 166:return "\"node70\"";case 19:return "\"node49\"";case 69:return "\"node72\"";case 213:return "\"node75\"";case 194:return "\"node142\"";case 221:return "\"node150\"";case 99:return "\"node60\"";case 190:return "\"node61\"";}throw runtime_error("unknown leaf");}
 void save(int root,string path){ofstream out(path);auto v=reachable(root);out<<"{\"root\":\"g"<<root<<"\",\"rules\":{";bool first=true;for(auto t:v){auto n=ns[t];if(!first)out<<',';first=false;auto str=[&](int c){return c<0?jsonleaf(c):"\"g"+to_string(c)+"\"";};out<<"\"g"<<t<<"\":["<<str(n.l)<<','<<str(n.r)<<']';}out<<"}}\n";}
};
struct S{int root;array<int,6>p;int score,eff,n,fold,pen;array<int,6>ord{0,1,2,3,4,5};};
S scored(E&e,int root,array<int,6>p,array<int,6>ord={0,1,2,3,4,5}){auto v=e.evaluate(root);auto a=e.at(root);int pen=4*a.bad+4*max(a.m-6,0)+4*max(a.mi-5,0)+max(a.h-38,0);return {root,p,v.effective+pen,v.effective,v.n,v.fold,pen,ord};}

int main(int argc,char**argv){
 if(argc<4)return 2; use_compatible=true;ifstream in(argv[1]);int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;int nt;in>>nt;vector<int>roots;for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<int>v(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;v[i]=t.op?e.pair(v[t.a],v[t.b]):leaf(t.a);}roots.push_back(v[rt]);}
 string out=argv[3];long long checks=0,hits=0;auto start=chrono::steady_clock::now();
 function<int(int,string const&,size_t,int)>at=[&](int t,string const&p,size_t i,int fresh){if(i==p.size())return fresh;auto n=e.ns[t];if(p[i]=='0')return e.pair(at(n.l,p,i+1,fresh),n.r);return e.pair(n.l,at(n.r,p,i+1,fresh));};
 auto neighbors=[&](int root,bool global){vector<pair<int,string>>ans;unordered_set<int>visited;
  function<void(int,string)>go=[&](int t,string p){if(t<0)return;if(global&&!visited.insert(t).second)return;auto n=e.ns[t];
   if(n.l>=0){auto a=e.ns[n.l];int fresh=e.pair(a.l,e.pair(a.r,n.r));ans.push_back({global?e.replace(root,t,fresh):at(root,p,0,fresh),p+"R"});}
   if(n.r>=0){auto a=e.ns[n.r];int fresh=e.pair(e.pair(n.l,a.l),a.r);ans.push_back({global?e.replace(root,t,fresh):at(root,p,0,fresh),p+"L"});}
   go(n.l,p+"0");go(n.r,p+"1");};go(root,"");return ans;};
 for(int seed=0;seed<int(roots.size());seed++){ bool global=false;
  int root=roots[seed];unordered_set<int>seen;seen.insert(root);long long cases=0;int best=999;
  auto test=[&](int r,string witness){if(!seen.insert(r).second)return;auto sc=scored(e,r,{});checks++;cases++;best=min(best,sc.eff);
   if(sc.eff<=60){string path=out+".hit"+to_string(hits)+".grammar.json";e.save(r,path);cout<<"HIT "<<hits++<<" seed "<<seed<<" mixed_all "<<true<<" score "<<sc.score<<" effective "<<sc.eff<<" raw "<<sc.n<<" folds "<<sc.fold<<" witness "<<witness<<endl;}
  };
  auto first=neighbors(root,false);auto first_global=neighbors(root,true);first.insert(first.end(),first_global.begin(),first_global.end());
  for(auto [r,w]:first){test(r,w);auto second=neighbors(r,false);auto second_global=neighbors(r,true);second.insert(second.end(),second_global.begin(),second_global.end());for(auto [rr,ww]:second)test(rr,w+","+ww);}
  cout<<"NEIGHBORHOOD seed "<<seed<<" mixed_all "<<true<<" first "<<first.size()<<" unique_cases "<<cases<<" best "<<best<<endl;
 }
 cout<<"DONE checks "<<checks<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
