#define PARAMETER_SCREEN_NO_MAIN
#include "screen.cpp"
#include <numeric>
int main(int argc,char**argv){
 if(argc<2)return 2;use_compatible=true;
 ifstream in(argv[1]);int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 int nt;in>>nt;int id,n,rt;in>>id>>n>>rt;vector<T>ts(n);for(auto&t:ts)in>>t.op>>t.a>>t.b>>t.c;
 int SK[]={51,36,25,48,32,33,22,55,60};vector<pair<int,int>> patch;
 for(int q:base){if(find(begin(SK),end(SK),q)!=end(SK))continue;for(int i=0;i<9;i++)if(rows[q][1].n==SK[i]&&rows[q][1].w==0&&rows[q][1].d==1)patch.push_back({q,i});}
 array<int,9>p; iota(p.begin(),p.end(),0);int count=0,best=999;auto start=chrono::steady_clock::now();
 do{for(auto[q,i]:patch)rows[q][1].n=SK[p[i]];auto v=calc(ts,rt,{});count++;if(v.effective<best){best=v.effective;cout<<"BEST "<<best<<" nodes "<<v.n<<" folds "<<v.fold<<" layout ";for(int x:p)cout<<x;cout<<" case "<<count<<endl;}if(v.effective<60){cout<<"HIT ";for(int x:p)cout<<x;cout<<' '<<v.effective<<endl;}}
 while(next_permutation(p.begin(),p.end()));
 cout<<"DONE "<<count<<" best "<<best<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
