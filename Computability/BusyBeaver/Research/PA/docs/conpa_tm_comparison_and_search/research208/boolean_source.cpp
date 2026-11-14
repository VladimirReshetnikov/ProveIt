#include <fstream>
#include <iostream>
#include <vector>
#include <array>
#include <queue>
using namespace std;
struct I{int op,r,z,p;};
int main(int argc,char**argv){
 ifstream f(argv[1]);int n,start;f>>n>>start;vector<I> ins(n);for(auto&i:ins)f>>i.op>>i.r>>i.z>>i.p;
 vector<array<bool,512>> seen(n);queue<pair<int,int>> todo;
 auto add=[&](int pc,int m){if(!seen[pc][m]){seen[pc][m]=true;todo.emplace(pc,m);}};
 add(start,1);int count=0;
 while(!todo.empty()){
  auto[pc,m]=todo.front();todo.pop();count++;auto i=ins[pc];int bit=1<<i.r;
  if(i.op==0)add(i.p,m|bit);
  if(i.op==1){if(m&bit){add(i.p,m);add(i.p,m&~bit);}else add(i.z,m);}
  if(i.op==2)add(i.p,m);
 }
 array<array<bool,9>,9> conflict{};int reached=0;
 cout<<"states "<<count<<endl;
 for(int pc=0;pc<n;pc++){
  bool any=false,zero=false,positive=false;auto i=ins[pc];
  for(int m=0;m<512;m++)if(seen[pc][m]){
   any=true;int bit=1<<i.r;zero|=!(m&bit);positive|=bool(m&bit);
   if(i.op<2)for(int r=0;r<9;r++)if(r!=i.r&&(m&(1<<r)))conflict[i.r][r]=conflict[r][i.r]=true;
  }
  if(any)reached++;
  else cout<<"UNREACHED "<<pc<<endl;
  if(any&&i.op==1&&!(zero&&positive))cout<<"BRANCH "<<pc<<" register "<<i.r<<" zero "<<zero<<" positive "<<positive<<endl;
 }
 cout<<"reached PCs "<<reached<<endl;
 for(int a=0;a<9;a++)for(int b=a+1;b<9;b++)if(!conflict[a][b])cout<<"COALESCE "<<a<<" "<<b<<endl;
}
