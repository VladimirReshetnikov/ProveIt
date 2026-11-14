#define main inherited_main
#include "search_plateau.cpp"
#undef main
int main(int argc,char**argv){
 if(argc<6){cerr<<"bin_grammar input attrs productions prefix seconds [seed]\n";return 2;}
 use_compatible=true;ifstream in(argv[1]);int nb;in>>nb;for(int j=0;j<nb;j++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 ifstream ip(argv[3]);int np;ip>>np;vector<vector<pair<int,int>>>prod(np);for(int i=0;i<np;i++){int n;ip>>n;prod[i].resize(n);for(auto &p:prod[i])ip>>p.first>>p.second;}
 string out=argv[4];double seconds=atof(argv[5]);uint64_t seed=argc>6?strtoull(argv[6],0,10):2026111410;mt19937_64 rng(seed);auto start=chrono::steady_clock::now();auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};int best=999;long long proposals=0;ofstream log(out+".jsonl");
 while(elapsed()<seconds){
  E e;vector<int>val(np);for(int i=0;i<np;i++){vector<int>children;for(auto [kind,v]:prod[i])children.push_back(kind?val[v]:leaf(v));
   function<int(int,int)>bin=[&](int l,int r){if(l+1==r)return children[l];int k=l+1+rng()%(r-l-1);return e.pair(bin(l,k),bin(k,r));};val[i]=bin(0,children.size());}
  auto s=scored(e,val.back(),{});proposals++;if(s.score<best){best=s.score;e.save(val.back(),out+".best.grammar.json");cout<<"BEST "<<best<<" raw "<<s.n<<" folds "<<s.fold<<" penalty "<<s.pen<<" proposals "<<proposals<<" seconds "<<elapsed()<<endl;}
  if(s.score<60&&!s.pen)break;
 }
 cout<<"DONE proposals "<<proposals<<" best "<<best<<" seconds "<<elapsed()<<endl;
}
