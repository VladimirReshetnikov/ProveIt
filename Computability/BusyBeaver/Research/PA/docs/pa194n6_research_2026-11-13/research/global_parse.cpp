#define main inherited_main
#include "search_plateau.cpp"
#undef main
#include <climits>

// Fixed-word global reparsing. The finite search is not a correctness proof.
struct Span { int i,n,freq; vector<int> cuts; };
int main(int argc,char**argv){
 if(argc<5){cerr<<"global_parse input attrs prefix seconds [seed]\n";return 2;}
 use_compatible=true;
 ifstream in(argv[1]);int nb;in>>nb;for(int j=0;j<nb;j++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;vector<int> seeds;int nt;in>>nt;for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<int>vs(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;vs[i]=t.op?e.pair(vs[t.a],vs[t.b]):leaf(t.a);}seeds.push_back(vs[rt]);}
 vector<int> w;function<void(int)>flatten=[&](int t){if(t>=0){flatten(e.ns[t].l);flatten(e.ns[t].r);}else {int q=physical(t);if(q==99){w.push_back(61);w.push_back(61);}else if(q==190){for(int j=0;j<4;j++)w.push_back(61);}else w.push_back(q);}};flatten(seeds[0]);
 const int N=w.size(); vector<vector<int>>sid(N,vector<int>(N+1,-1)); vector<Span> sp;map<vector<int>,int> lookup;
 for(int len=1;len<=N;len++)for(int i=0;i+len<=N;i++){vector<int>word(w.begin()+i,w.begin()+i+len);auto [it,fresh]=lookup.emplace(word,sp.size());if(fresh)sp.push_back({i,len,0,{}});sid[i][len]=it->second;sp[it->second].freq++;}
 for(auto&s:sp)for(int k=1;k<s.n;k++)s.cuts.push_back(k);
 uint64_t seed=argc>5?strtoull(argv[5],0,10):2026111408;mt19937_64 rng(seed);auto uni=[&](){return generate_canonical<double,53>(rng);};normal_distribution<double>norm(0.,1.);
 string out=argv[3];double seconds=atof(argv[4]);auto start=chrono::steady_clock::now();auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 int best=999,bestRaw=999;long long proposals=0;vector<int>pool=seeds;ofstream log(out+".jsonl");
 for(int root:seeds){auto s=scored(e,root,{});best=min(best,s.score);bestRaw=min(bestRaw,s.n);}
 cout<<"INITIAL word "<<N<<" substrings "<<sp.size()<<" best "<<best<<endl;
 vector<double>cost(sp.size()),own(sp.size());vector<int>val(sp.size());vector<Attr>attr(sp.size());
 while(elapsed()<seconds){
  proposals++;
  // Re-estimate repetition weights from the previous good parse, mixed with
  // all available substring occurrences. This changes every split at once.
  unordered_map<int,int> usage;int old=pool[rng()%pool.size()];
  function<void(int,int)> count=[&](int t,int i){if(t<0){return;}auto n=e.ns[t];int len=e.at(t).len; if(i+len<=N)usage[sid[i][len]]++;count(n.l,i);count(n.r,i+e.at(n.l).len);};
  // Input leaf 99/190 compression alters at.len. Use only all-substring
  // weights in this release to keep the scoring definition unambiguous.
  double power=.40+1.10*uni(),noise=.10+1.4*uni();
  for(int s=0;s<(int)sp.size();s++){
   const auto&a=sp[s]; own[s]=exp(noise*norm(rng))/pow(double(a.freq),power);
   if(a.n==1){cost[s]=0;val[s]=leaf(w[a.i]);attr[s]=e.at(val[s]);continue;}
   cost[s]=1e100;val[s]=INT_MIN;
   for(int k:a.cuts){int l=sid[a.i][k],r=sid[a.i+k][a.n-k];if(val[l]==INT_MIN||val[r]==INT_MIN)continue;
    Attr x=attr[l],y=attr[r],z;z.h=1+max(x.h,y.h);z.l=x.l+1;z.m=max({x.l+1,x.m,y.m});z.mi=max({x.mi,y.mi,x.inc?1+x.l:0});z.inc=x.inc;z.len=a.n;z.bad=x.bad+y.bad+((val[l]<0&&physical(val[l])==194)?1:0)+((val[r]<0&&physical(val[r])==69)?1:0);
    if(z.bad||z.m>6||z.mi>5||z.h>38)continue;
    bool freePair=(a.n==2&&w[a.i]==61&&w[a.i+1]==61)||(a.n==4&&w[a.i]==61&&w[a.i+1]==61&&w[a.i+2]==61&&w[a.i+3]==61&&k==2);
    double v=cost[l]+cost[r]+(freePair?0:own[s]);
    if(v<cost[s]){cost[s]=v;val[s]=e.pair(val[l],val[r]);attr[s]=z;}
   }
  }
  int root=val[sid[0][N]];if(root!=INT_MIN){S s=scored(e,root,{});if(s.score<best||s.n<bestRaw){if(s.score<best){best=s.score;e.save(root,out+".best.grammar.json");}bestRaw=min(bestRaw,s.n);cout<<"BEST "<<s.score<<" raw "<<s.n<<" folds "<<s.fold<<" proposal "<<proposals<<" seconds "<<elapsed()<<endl;log<<"{\"proposal\":"<<proposals<<",\"score\":"<<s.score<<",\"raw\":"<<s.n<<",\"folds\":"<<s.fold<<",\"seconds\":"<<elapsed()<<"}\n";log.flush();}
   if(s.score<=60&&!s.pen){e.save(root,out+".hit"+to_string(proposals)+".grammar.json");pool.push_back(root);if(pool.size()>200)pool.erase(pool.begin()+seeds.size());}
   if(s.score<60&&!s.pen)break;
  }
  if(proposals%50==0){E clean;unordered_map<int,int>memo;function<int(int)>copy=[&](int t){if(t<0)return t;auto it=memo.find(t);if(it!=memo.end())return it->second;auto n=e.ns[t];return memo[t]=clean.pair(copy(n.l),copy(n.r));};for(auto&r:pool)r=copy(r);for(auto&r:seeds)r=copy(r);e=move(clean);}
  if(proposals%100==0)cout<<"PROGRESS "<<proposals<<" best "<<best<<" seconds "<<elapsed()<<endl;
 }
 cout<<"DONE proposals "<<proposals<<" best "<<best<<" minRaw "<<bestRaw<<" seconds "<<elapsed()<<endl;
}
