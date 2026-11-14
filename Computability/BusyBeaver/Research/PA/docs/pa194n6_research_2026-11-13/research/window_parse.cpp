#define main inherited_main
#include "search_plateau.cpp"
#undef main
#include <climits>

// Fixed-word subtree reparsing against a live shared dictionary. This move
// changes an arbitrary bracketed region, rather than one rotation.
int main(int argc,char**argv){
 if(argc<5){cerr<<"window_parse input attrs prefix seconds [seed]\n";return 2;}
 use_compatible=true;
 ifstream in(argv[1]);int nb;in>>nb;for(int j=0;j<nb;j++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;vector<S>pool;int nt;in>>nt;for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<int>vs(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;if(t.op)vs[i]=e.pair(vs[t.a],vs[t.b]);else if(t.a==99)vs[i]=e.pair(leaf(61),leaf(61));else if(t.a==190){int a=e.pair(leaf(61),leaf(61));vs[i]=e.pair(a,a);}else vs[i]=leaf(t.a);}pool.push_back(scored(e,vs[rt],{}));}
 uint64_t seed=argc>5?strtoull(argv[5],0,10):2026111409;mt19937_64 rng(seed);auto uni=[&](){return generate_canonical<double,53>(rng);};
 string out=argv[3];double seconds=atof(argv[4]);auto start=chrono::steady_clock::now();auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 int best=999;long long proposals=0,accepted=0,hits=0;ofstream log(out+".jsonl");for(auto s:pool)best=min(best,s.score);S cur=pool[0];
 cout<<"INITIAL best "<<best<<endl;
 while(elapsed()<seconds){
  proposals++;
  if(proposals%100==1){sort(pool.begin(),pool.end(),[](S a,S b){return a.score<b.score;});cur=pool[rng()%min(int(pool.size()),40)];}
  auto reached=e.reachable(cur.root);int old=reached[rng()%reached.size()];
  if(e.at(old).len<4||e.at(old).len>85)continue;
  unordered_map<int,vector<int>>words;function<vector<int>const&(int)> word=[&](int t)->vector<int>const&{auto it=words.find(t);if(it!=words.end())return it->second;vector<int> v;if(t<0)v={physical(t)};else{auto n=e.ns[t];auto a=word(n.l),b=word(n.r);v=a;v.insert(v.end(),b.begin(),b.end());}return words.emplace(t,move(v)).first->second;};
  vector<int>w=word(old);const int N=w.size();
  map<vector<int>,vector<int>>dict;for(int t:reached)if(t!=old&&uni()>.15)dict[word(t)].push_back(t);
  vector<vector<double>>cost(N,vector<double>(N+1,1e100));vector<vector<int>>val(N,vector<int>(N+1,INT_MIN));
  double noise=.05+.9*uni();
  for(int len=1;len<=N;len++)for(int i=0;i+len<=N;i++){
   if(len==1){cost[i][len]=0;val[i][len]=leaf(w[i]);continue;}
   vector<int> sw(w.begin()+i,w.begin()+i+len);auto dit=dict.find(sw);if(dit!=dict.end()){val[i][len]=dit->second[rng()%dit->second.size()];cost[i][len]=noise*uni();}
   for(int k=1;k<len;k++){int l=val[i][k],r=val[i+k][len-k];if(l==INT_MIN||r==INT_MIN)continue;
    Attr x=e.at(l),y=e.at(r);int h=1+max(x.h,y.h),m=max({x.l+1,x.m,y.m}),mi=max({x.mi,y.mi,x.inc?1+x.l:0});int bad=x.bad+y.bad+((l<0&&physical(l)==194)?1:0)+((r<0&&physical(r)==69)?1:0);if(bad||m>6||mi>5||h>38)continue;
    bool freePair=(len==2&&w[i]==61&&w[i+1]==61)||(len==4&&w[i]==61&&w[i+1]==61&&w[i+2]==61&&w[i+3]==61&&k==2);
    double c=cost[i][k]+cost[i+k][len-k]+(freePair?0:1)+noise*uni();
    if(c<cost[i][len]){cost[i][len]=c;val[i][len]=e.pair(l,r);}
   }
  }
  if(val[0][N]==INT_MIN)continue;int root=e.replace(cur.root,old,val[0][N]);S ns=scored(e,root,{});
  double temp=.10+.4*uni();if(ns.score<=cur.score||uni()<exp((cur.score-ns.score)/temp)){cur=ns;accepted++;
   if(ns.score<best){best=ns.score;e.save(root,out+".best.grammar.json");cout<<"BEST "<<best<<" raw "<<ns.n<<" folds "<<ns.fold<<" proposal "<<proposals<<" seconds "<<elapsed()<<endl;}
   if(ns.score<=best+1&&!ns.pen&&pool.size()<2000)pool.push_back(ns);
   if(ns.score<60&&!ns.pen){e.save(root,out+".hit.grammar.json");break;}
  }
  if(proposals%500==0){sort(pool.begin(),pool.end(),[](S a,S b){return a.score<b.score;});if(pool.size()>250)pool.resize(250);E clean;unordered_map<int,int>memo;function<int(int)>copy=[&](int t){if(t<0)return t;auto it=memo.find(t);if(it!=memo.end())return it->second;auto n=e.ns[t];int l=copy(n.l),r=copy(n.r);int v=clean.pair(l,r);memo[t]=v;return v;};for(auto&s:pool)s.root=copy(s.root);cur.root=copy(cur.root);e=move(clean);cout<<"PROGRESS "<<proposals<<" accepted "<<accepted<<" best "<<best<<" seconds "<<elapsed()<<endl;}
 }
 cout<<"DONE proposals "<<proposals<<" accepted "<<accepted<<" best "<<best<<" seconds "<<elapsed()<<endl;
}
