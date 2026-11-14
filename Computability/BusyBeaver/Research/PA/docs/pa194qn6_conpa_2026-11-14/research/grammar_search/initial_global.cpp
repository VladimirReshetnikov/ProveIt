#define PARAMETER_SCREEN_NO_MAIN
#include "screen_global.cpp"
int main(int argc,char**argv){use_compatible=true;ifstream in(argv[1]);int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}int nt;in>>nt;for(int ti=0;ti<nt;ti++){int id,n,rt;in>>id>>n>>rt;vector<T> ts(n);for(auto&t:ts)in>>t.op>>t.a>>t.b>>t.c;auto r=calc(ts,rt,array<int,6>{});cout<<nb<<' '<<r.n<<' '<<r.fold<<' '<<nb+r.effective<<endl;}}
