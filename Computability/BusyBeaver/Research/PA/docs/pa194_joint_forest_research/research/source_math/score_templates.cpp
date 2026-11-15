#define main ignored_main
#include "search.cpp"
#undef main
int main(int argc,char**argv){
 ifstream in(argv[1]); int nb;in>>nb;
 for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 use_compatible=true; E e;int nt;in>>nt;cout<<"id,score,effective,raw,fold,penalty\n";
 for(int j=0;j<nt;j++){int id,n,rt;in>>id>>n>>rt;vector<int>vs(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;vs[i]=t.op?e.pair(vs[t.a],vs[t.b]):leaf(t.a);}auto s=scored(e,vs[rt],{});cout<<id<<','<<s.score<<','<<s.eff<<','<<s.n<<','<<s.fold<<','<<s.pen<<'\n'; if(s.score<=60)e.save(s.root,string(argv[3])+to_string(id)+".grammar.json");}
}
