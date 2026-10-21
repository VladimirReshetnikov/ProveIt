#include <bits/stdc++.h>
using namespace std;
struct Node {int a,b,br,co,lead,zr;};
vector<Node> ns;
unordered_map<unsigned long long,int> memo;
int add(int a,int b){
  unsigned long long key=(static_cast<unsigned long long>(static_cast<unsigned>(a))<<32)|static_cast<unsigned>(b);
  auto it=memo.find(key); if(it!=memo.end())return it->second;
  Node n{a,b,0,0,0,0};
  if(a<0){int op=-a-1; if(op==1)n.br=1;else if(op==2)n.br=b;else if(op==3)n.co=b;}
  else {n.br=max({ns[a].br-1,ns[b].br,0});n.co=max({ns[a].co,ns[b].co-1,0});n.lead=1+ns[a].lead;n.zr=max({n.lead,ns[a].zr,ns[b].zr});}
  int id=ns.size();ns.push_back(n);memo.emplace(key,id);return id;
}
vector<int> reach(int r){vector<int> v,st{r};unordered_set<int> seen;while(!st.empty()){int q=st.back();st.pop_back();if(!seen.insert(q).second)continue;v.push_back(q);if(ns[q].a>=0){st.push_back(ns[q].a);st.push_back(ns[q].b);}}return v;}
int replace_root(int r,int x,int y){unordered_map<int,int> cache;function<int(int)> f=[&](int q){if(q==x)return y;if(ns[q].a<0)return q;auto it=cache.find(q);if(it!=cache.end())return it->second;int a=ns[q].a,b=ns[q].b;int aa=f(a),bb=f(b);return cache[q]=add(aa,bb);};return f(r);}
struct Prev {int root,q,nq,kind;};
int main(int argc,char**argv){
 if(argc<3)return 1;ifstream f(argv[1]);int n,root;f>>n>>root;for(int i=0;i<n;i++){int a,b;f>>a>>b;if(add(a,b)!=i)return 2;}
 int seconds=argc>3?atoi(argv[3]):300;int seed=argc>4?atoi(argv[4]):218205;mt19937 rng(seed);
 unordered_set<int>seen{root};unordered_map<int,Prev>prev;vector<int>frontier{root};int best=n;long long trials=0;auto start=chrono::steady_clock::now();
 for(int depth=1;depth<500;depth++){
  vector<tuple<int,unsigned,int>> options;
  for(int rr:frontier){auto active=reach(rr);sort(active.begin(),active.end());
   for(int q:active){Node nd=ns[q];if(nd.a<0)continue;int a=nd.a,b=nd.b;
    vector<pair<int,int>>replacements;
    if(ns[a].a>=0){int aa=ns[a].a,ab=ns[a].b;if(ns[aa].br==0&&ns[b].co==0)replacements.push_back({0,add(aa,add(ab,b))});}
    if(ns[b].a>=0){int ba=ns[b].a,bb=ns[b].b;if(ns[a].br==0&&ns[bb].co==0)replacements.push_back({1,add(add(a,ba),bb)});}
    for(auto [kind,nq]:replacements){++trials;int nr=replace_root(rr,q,nq);if(!seen.insert(nr).second||ns[nr].zr>6)continue;int cost=reach(nr).size();if(cost>207)continue;prev[nr]={rr,q,nq,kind};options.emplace_back(cost,rng(),nr);
      if(cost<best){best=cost;cerr<<"BEST "<<cost<<" depth "<<depth<<" trial "<<trials<<" nodes "<<ns.size()<<endl;
       auto v=reach(nr);sort(v.begin(),v.end());unordered_map<int,int> ids;for(int i=0;i<(int)v.size();i++)ids[v[i]]=i;
       ofstream out(string(argv[2])+".dag");out<<v.size()<<" "<<ids[nr]<<"\n";for(int j:v){auto z=ns[j];out<<(z.a<0?z.a:ids[z.a])<<" "<<(z.a<0?z.b:ids[z.b])<<"\n";}out.close();
       if(best<=204)return 0;
      }
    }
   }
  }
  if(options.empty())break;sort(options.begin(),options.end());frontier.clear();unordered_set<int> chosen;
  int limits[3]={50,75,75};for(int c=205;c<=207;c++){int got=0;for(auto [cost,noise,r]:options)if(cost==c&&chosen.insert(r).second){frontier.push_back(r);if(++got>=limits[c-205])break;}}
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();cerr<<"DEPTH "<<depth<<" trial "<<trials<<" options "<<options.size()<<" frontier "<<frontier.size()<<" best "<<best<<" nodes "<<ns.size()<<" sec "<<elapsed<<endl;
  if(elapsed>seconds)break;
  if(ns.size()>2500000){
    vector<Node> old=move(ns);ns.clear();memo.clear();unordered_map<int,int> remap;
    function<int(int)> copy=[&](int q){auto it=remap.find(q);if(it!=remap.end())return it->second;Node z=old[q];int a=z.a,b=z.b;if(a>=0){a=copy(a);b=copy(b);}return remap[q]=add(a,b);};
    for(int &r:frontier)r=copy(r);root=copy(root);seen.clear();for(int r:frontier)seen.insert(r);prev.clear();
    cerr<<"COMPACT "<<ns.size()<<endl;
  }
 }
 cerr<<"DONE best "<<best<<" trials "<<trials<<" seen "<<seen.size()<<endl;
}
