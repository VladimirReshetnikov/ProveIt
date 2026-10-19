from pathlib import Path
HERE=Path(__file__).resolve().parent
s=(HERE/'anneal_semantic.cpp').read_text()
start=s.index('int main(')
extra=r'''
unordered_map<int,string>fineMemo;
string fineword(int q){
 auto it=fineMemo.find(q);if(it!=fineMemo.end())return it->second;
 string ret;
 for(char c:words[q]){bool done=false;for(auto[a,b]:aliases)if(b[0]==c){ret+=a;done=true;break;}if(!done)ret+=c;}
 fineMemo[q]=ret;return ret;
}
struct Opt{int cost=1000000,q=-1;};
int semantic_reparse(Grammar&g,const vector<int>&p,mt19937_64&rng){
 int n=p.size();if(!n||n>150)return -1;
 unordered_map<string,int> dict;
 for(auto[q,r]:g)dict[fineword(q)]=q;
 unordered_map<string,vector<int>> atoms;
 for(auto[c,m]:allowed)atoms[fineword(intern(string(1,c)))].push_back(intern(string(1,c)));
 vector<vector<array<Opt,2>>>dp(n,vector<array<Opt,2>>(n+1));
 vector<vector<string>> keys(n,vector<string>(n+1));
 for(int i=0;i<n;i++)for(int j=i+1;j<=n;j++)keys[i][j]=keys[i][j-1]+fineword(p[j-1]);
 for(int k=1;k<=n;k++)for(int i=0;i+k<=n;i++){
  int j=i+k;auto key=keys[i][j];
  auto di=dict.find(key);
  if(di!=dict.end()){for(int b=0;b<2;b++)dp[i][j][b]={0,di->second};continue;}
  auto ai=atoms.find(key);
  if(ai!=atoms.end())for(int a:ai->second)for(int b=0;b<2;b++)if(allowed[words[a][0]]&(1<<b))dp[i][j][b]={0,a};
  for(int h=i+1;h<j;h++){
   auto a=dp[i][h][0],b=dp[h][j][1];
   if(a.q<0||b.q<0)continue;
   int cost=a.cost+b.cost+1;
   if(cost>dp[i][j][0].cost&&cost>dp[i][j][1].cost)continue;
   int q=intern(words[a.q]+words[b.q]);
   if(!g.count(q))g[q]={a.q,b.q};
   for(int bit=0;bit<2;bit++)if(cost<dp[i][j][bit].cost||(cost==dp[i][j][bit].cost&&rng()%2))dp[i][j][bit]={cost,q};
  }
 }
 return dp[0][n][0].q;
}
bool semantic_delete(Grammar&g,vector<int>&route,mt19937_64&rng){
 unordered_set<int> protected_set;
 vector<int>todo=route;
 for(int i=0;i<(int)roots.size();i++)if(i!=ax_index)todo.push_back(roots[i]);
 while(!todo.empty()){int q=todo.back();todo.pop_back();if(terminal(q)||!protected_set.insert(q).second)continue;auto r=g.at(q);todo.push_back(r.a);todo.push_back(r.b);}
 vector<int>opts;for(auto[q,r]:g)if(!protected_set.count(q))opts.push_back(q);
 if(opts.empty())return false;
 int doomed=opts[rng()%opts.size()];
 unordered_set<int>bad{doomed};bool changed=true;
 while(changed){changed=false;for(auto[q,r]:g)if(!bad.count(q)&&(bad.count(r.a)||bad.count(r.b))){bad.insert(q);changed=true;}}
 if(!bad.count(roots[ax_index]))return false;
 vector<int>parts;todo={roots[ax_index]};
 while(!todo.empty()){int q=todo.back();todo.pop_back();if(!bad.count(q)){parts.push_back(q);continue;}auto r=g.at(q);todo.push_back(r.b);todo.push_back(r.a);}
 for(int q:bad)g.erase(q);
 int root=semantic_reparse(g,parts,rng);if(root<0)return false;
 roots[ax_index]=root;return true;
}
'''
s=s[:start]+extra+s[start:]
s=s.replace('#include <algorithm>','#include <algorithm>\n#include <array>')
s=s.replace('if(rng()%1000<5)changed=rewrite_move(next,nextroute,rng);','int special=rng()%1000;\n if(special<3)changed=semantic_delete(next,nextroute,rng);\n else if(special<5)changed=rewrite_move(next,nextroute,rng);')
s=s.replace('<<" pool "<<words.size()<<endl;', '<<" pool "<<words.size()<<" AX "<<words[roots[ax_index]].size()<<endl;')
(HERE/'anneal_semantic_delete.cpp').write_text(s)
