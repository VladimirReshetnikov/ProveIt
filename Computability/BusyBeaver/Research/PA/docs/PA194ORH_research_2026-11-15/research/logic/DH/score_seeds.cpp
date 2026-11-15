#define PARAMETER_SCREEN_NO_MAIN
#include "screen.cpp"
int main(int argc,char**argv){
 if(argc!=2)return 2;
 use_compatible=true;ifstream in(argv[1]);int nb;in>>nb;
 for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;
  for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 int nt;in>>nt;cout<<"seed,raw_readers,reported_fold_count,effective_reader_score,working_state_score,simultaneous_compatibility_checked\n";
 for(int i=0;i<nt;i++){int tid,n,rt;in>>tid>>n>>rt;vector<T>ts(n);
  for(auto &t:ts)in>>t.op>>t.a>>t.b>>t.c;
  use_compatible=false;auto optimistic=calc(ts,rt,array<int,6>{});
  use_compatible=true;auto z=calc(ts,rt,array<int,6>{});
  cout<<tid<<','<<z.n<<','<<z.fold<<','<<z.effective<<','<<nb+z.effective
      <<','<<(optimistic.effective<=64 ? "true" : "false")<<'\n';}
}
