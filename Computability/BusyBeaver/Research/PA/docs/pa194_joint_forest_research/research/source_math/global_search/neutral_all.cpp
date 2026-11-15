#define main ignored_main
#include "search_all.cpp"
#undef main
#include <deque>
struct Hash2 {uint64_t a,b;bool operator==(Hash2 const&v)const{return a==v.a&&b==v.b;}};
struct HKey {size_t operator()(Hash2 const&v)const{return v.a^(v.b>>1);}};
uint64_t mix(uint64_t v){v^=v>>30;v*=0xbf58476d1ce4e5b9ULL;v^=v>>27;v*=0x94d049bb133111ebULL;return v^(v>>31);}
int main(int argc,char**argv){
 if(argc<6){cerr<<"neutral templates attrs output-prefix max-evals max-seconds\n";return 2;}
 use_compatible=true;ifstream in(argv[1]);int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;vector<Hash2>hm;auto lh=[](int t){return Hash2{mix(uint64_t(t)+7919),mix(uint64_t(t)+23911)};};
 auto hashroot=[&](int t){for(int i=hm.size();i<int(e.ns.size());i++){auto n=e.ns[i];auto a=n.l<0?lh(n.l):hm[n.l],b=n.r<0?lh(n.r):hm[n.r];hm.push_back({mix(a.a+3*b.a+23),mix(a.b+7*b.b+41)});}return t<0?lh(t):hm[t];};
 vector<deque<S>>queue(100);unordered_set<Hash2,HKey>seen;long long evaluated=0,admitted=0,popped=0,skipped=0;int best=999;string out=argv[3];
 int nt;in>>nt;for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<int>values(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;values[i]=t.op?e.pair(values[t.a],values[t.b]):leaf(t.a);}auto s=scored(e,values[rt],{});if(s.pen)continue;best=min(best,s.score);if(s.score<=59&&seen.insert(hashroot(s.root)).second){queue[s.score].push_back(s);admitted++;}}
 cout<<"INITIAL best "<<best<<" admitted "<<admitted<<endl;
 auto start=chrono::steady_clock::now();auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};long long cap=atoll(argv[4]);double sec=atof(argv[5]);
 bool stop=false;int hits=0;
 auto candidate=[&](int t){auto a=e.at(t);if(a.bad||a.m>6||a.mi>5||a.h>38){skipped++;return;}
  if(!seen.insert(hashroot(t)).second)return;auto s=scored(e,t,{});evaluated++;
  if(s.score<best){best=s.score;e.save(s.root,out+".best.grammar.json");cout<<"BEST "<<best<<" effective "<<s.eff<<" raw "<<s.n<<" folds "<<s.fold<<" eval "<<evaluated<<" seconds "<<elapsed()<<endl;}
  if(!s.pen&&s.score<=59){queue[s.score].push_back(s);admitted++;if(s.eff<=57){e.save(s.root,out+".hit"+to_string(hits++)+".grammar.json");stop=true;}}
  if(evaluated>=cap||elapsed()>sec)stop=true;
 };
 while(!stop){int k=0;while(k<100&&queue[k].empty())k++;if(k==100)break;S s=queue[k].front();queue[k].pop_front();popped++;
  auto reach=e.reachable(s.root);
  for(int x:reach){auto n=e.ns[x];if(n.l>=0){auto a=e.ns[n.l];candidate(e.replace(s.root,x,e.pair(a.l,e.pair(a.r,n.r))));}if(n.r>=0){auto a=e.ns[n.r];candidate(e.replace(s.root,x,e.pair(e.pair(n.l,a.l),a.r)));}if(stop)break;}
  for(int j=0;!stop&&j<e.at(s.root).len-1;j++){int x=e.occurrence(s.root,j);auto n=e.ns[x];if(n.l>=0){auto a=e.ns[n.l];candidate(e.replace_one(s.root,j,e.pair(a.l,e.pair(a.r,n.r))));}if(n.r>=0){auto a=e.ns[n.r];candidate(e.replace_one(s.root,j,e.pair(e.pair(n.l,a.l),a.r)));}}
  if(popped%100==0)cout<<"PROGRESS popped "<<popped<<" eval "<<evaluated<<" seen "<<seen.size()<<" admitted "<<admitted<<" best "<<best<<" seconds "<<elapsed()<<endl;
  if(e.ns.size()>200000){E clean;unordered_map<int,int>mem;function<int(int)>copy=[&](int t){if(t<0)return t;auto it=mem.find(t);if(it!=mem.end())return it->second;auto n=e.ns[t];int l=copy(n.l),r=copy(n.r),z=clean.pair(l,r);mem[t]=z;return z;};for(auto &q:queue)for(auto &v:q)v.root=copy(v.root);e=move(clean);hm.clear();}
 }
 for(int sc=0;sc<60;sc++){int j=0;for(auto s:queue[sc]){if(j>=20)break;e.save(s.root,out+".score"+to_string(sc)+".seed"+to_string(j++)+".grammar.json");}}
 cout<<"DONE best "<<best<<" evaluated "<<evaluated<<" admitted "<<admitted<<" popped "<<popped<<" seen "<<seen.size()<<" skippedlayout "<<skipped<<" hits "<<hits<<" seconds "<<elapsed()<<endl;
}
