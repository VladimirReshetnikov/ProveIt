#define main inherited_joint_main
#include "search_J_full_order.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=4){cerr<<"price_J_orders templates attrs output_prefix\n";return 2;}
 use_compatible=true;
 ifstream in(argv[1]);int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;int nt;in>>nt;vector<int>roots;for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<int>values(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;values[i]=t.op?e.pair(values[t.a],values[t.b]):leaf(t.a);}roots.push_back(values[rt]);}
 int best=999,count=0;ofstream csv(string(argv[3])+".csv");csv<<"template,order,score,effective,readers,folds,penalty\n";
 for(int root:roots){array<int,6>desired={0,1,2,3,4,5};do{
  array<int,6>order={0,1,2,3,4,5};int nr=root;
  for(int i=0;i<6;i++){int j=i;while(order[j]!=desired[i])j++;if(i!=j){nr=e.swap_heads(nr,order,i,j);swap(order[i],order[j]);}}
  S r=scored(e,nr,{},order);csv<<count/720<<',';for(int h:order)csv<<h;csv<<','<<r.score<<','<<r.eff<<','<<r.n<<','<<r.fold<<','<<r.pen<<'\n';
  if(r.score<best){best=r.score;e.save(nr,string(argv[3])+".best.grammar.json");cout<<"BEST score "<<best<<" effective "<<r.eff<<" penalty "<<r.pen<<" order ";for(int h:order)cout<<h;cout<<endl;}
  count++;
 }while(next_permutation(desired.begin(),desired.end()));}
 cout<<"DONE candidates "<<count<<" best "<<best<<endl;
}
