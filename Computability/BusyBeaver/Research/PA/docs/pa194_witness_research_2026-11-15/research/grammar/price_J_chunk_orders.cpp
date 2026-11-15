#define main inherited_joint_main
#include "search_J_full_order.cpp"
#undef main
#include <climits>
int main(int argc,char**argv){
 if(argc!=4){cerr<<"price_J_chunk_orders templates attrs output_prefix\n";return 2;}
 use_compatible=true;
 ifstream in(argv[1]);int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;int nt;in>>nt;vector<int>roots;for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<int>values(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;values[i]=t.op?e.pair(values[t.a],values[t.b]):leaf(t.a);}roots.push_back(values[rt]);}
 int best=999,count=0,min_effective=999;ofstream csv(string(argv[3])+".csv");csv<<"template,order,best_score,effective,readers,folds,penalty,shapes\n";
 auto slice=[&](int root,int low,int high){
  function<int(int,int)>go=[&](int t,int pos){int len=e.at(t).len;if(pos+len<=low||pos>=high)return INT_MAX;if(pos>=low&&pos+len<=high)return t;auto nd=e.ns[t];int l=go(nd.l,pos),r=go(nd.r,pos+e.at(nd.l).len);return l==INT_MAX?r:r==INT_MAX?l:e.pair(l,r);};return go(root,0);
 };
 int ti=0;
 for(int root:roots){
  int lens[]={18,16,19,16,16,15,19,69},cursor=0;vector<int>parts;
  for(int len:lens){parts.push_back(slice(root,cursor,cursor+len));cursor+=len;}if(cursor!=188)throw runtime_error("length");
  array<int,6>order={0,1,2,3,4,5};do{
   vector<int>chunks={parts[0]};for(int h:order)chunks.push_back(parts[h+1]);chunks.push_back(parts[7]);
   map<pair<int,int>,vector<int>>memo;
   function<vector<int>(int,int)>combine=[&](int l,int r){auto key=make_pair(l,r);if(memo.count(key))return memo[key];vector<int>ans;if(r-l==1)ans.push_back(chunks[l]);else for(int k=l+1;k<r;k++)for(int a:combine(l,k))for(int b:combine(k,r))ans.push_back(e.pair(a,b));return memo[key]=ans;};
   auto candidates=combine(0,8);S local;local.score=999;
   for(int nr:candidates){S r=scored(e,nr,{},order);count++;if(r.score<local.score)local=r;
    if(r.eff<min_effective){min_effective=r.eff;e.save(nr,string(argv[3])+".best_effective.grammar.json");auto aa=e.at(nr);cout<<"MIN_EFFECTIVE "<<min_effective<<" penalty "<<r.pen<<" height "<<aa.h<<" left_depth "<<aa.m<<" inc_left_depth "<<aa.mi<<" bad "<<aa.bad<<" candidates "<<count<<endl;}
    if(r.score<best){best=r.score;e.save(nr,string(argv[3])+".best.grammar.json");cout<<"BEST score "<<best<<" effective "<<r.eff<<" penalty "<<r.pen<<" order ";for(int h:order)cout<<h;cout<<" candidates "<<count<<endl;}}
   csv<<ti<<',';for(int h:order)csv<<h;csv<<','<<local.score<<','<<local.eff<<','<<local.n<<','<<local.fold<<','<<local.pen<<','<<candidates.size()<<'\n';
  }while(next_permutation(order.begin(),order.end()));ti++;
 }
 cout<<"DONE candidates "<<count<<" best "<<best<<" minimum_effective "<<min_effective<<endl;
}
