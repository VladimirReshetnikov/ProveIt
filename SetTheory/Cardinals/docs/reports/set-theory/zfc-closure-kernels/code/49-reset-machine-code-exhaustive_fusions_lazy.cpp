#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
struct E {int w,d,t;};
struct C {int state,pattern; vector<uint64_t> keys;};
int N,R,K; vector<array<E,2>> T; vector<vector<int>> W;
uint64_t key(int q,int h,int p) {return q==N ? UINT64_MAX : (uint64_t(q)<<40)|(uint64_t(h+64)<<32)|uint64_t(p);}
C condition(int state,int pattern,int removed,int retained) {
 C c{state,pattern,{}}; int q=state,h=0,p=pattern;
 for(int i=0;i<K && q!=N && abs(h)<=R;++i) {
  int bit=h+R; E a=T[q][(p>>bit)&1]; p=(p&~(1<<bit))|(a.w<<bit); h+=a.d; q=a.t;
  c.keys.push_back(key(q==removed?retained:q,h,p));
 }
 sort(c.keys.begin(),c.keys.end()); c.keys.erase(unique(c.keys.begin(),c.keys.end()),c.keys.end()); return c;
}
// 0 means no bounded match, 1 a positive match, 2 an unassigned row needed.
int execute(const C& c,int removed,int retained,const E* zero,const E* one) {
 int q=retained,h=0,p=c.pattern; uint64_t visited[256]; int nv=0;
 for(int i=0;i<K && q!=N && abs(h)<=R;++i) {
  uint64_t here=key(q,h,p);
  for(int j=0;j<nv;++j) if(visited[j]==here) return 0;
  visited[nv++]=here;
  int bit=h+R,b=(p>>bit)&1; E a;
  if(q==retained) { const E* x=b?one:zero; if(!x) return 2; a=*x; } else a=T[q][b];
  p=(p&~(1<<bit))|(a.w<<bit); h+=a.d; q=a.t==removed?retained:a.t;
  if(binary_search(c.keys.begin(),c.keys.end(),key(q,h,p))) return 1;
 }
 return 0;
}
int main(int argc,char**argv) {
 if(argc!=3) {cerr<<"usage: exhaustive_fusions input output_prefix\n"; return 2;}
 ifstream in(argv[1]); in>>N>>R>>K; if(!in || N<2 || N>1000 || R<1 || R>12 || K<1 || K>256) return 3;
 T.resize(N); W.resize(N+1);
 for(int q=0;q<N;++q)for(int b=0;b<2;++b)in>>T[q][b].w>>T[q][b].d>>T[q][b].t;
 for(int q=0;q<=N;++q){int n; in>>n; W[q].resize(n);for(int& p:W[q])in>>p;}
 if(!in) return 4;
 ofstream ledger(string(argv[2])+".tsv"); ledger<<"removed\tretained\tzero_domain\tone_domain\tfull_recipes\tcertificates\n";
 auto began=chrono::steady_clock::now(); uint64_t partial_checks=0,full_checks=0,pair_count=0,recipe_count=0,cert_count=0;
 ofstream certs(string(argv[2])+"_certificates.tsv");certs<<"removed\tretained\tw0\td0\tt0\tw1\td1\tt1\n";
 for(int removed=0;removed<N;++removed)for(int retained=removed+1;retained<N;++retained) {
  vector<E> actions; for(int w=0;w<2;++w)for(int d:{-1,1})for(int t=0;t<=N;++t)if(t!=removed)actions.push_back({w,d,t});
  vector<C> cs[2]; for(int s:{removed,retained})for(int p:W[s])cs[(p>>R)&1].push_back(C{s,p,{}});
  vector<int> allowed[2]; bool impossible=false;
  for(int b=0;b<2;++b) {
   allowed[b].resize(actions.size());iota(allowed[b].begin(),allowed[b].end(),0);
   for(C& c:cs[b]) {
    if(c.keys.empty())c=condition(c.state,c.pattern,removed,retained);
    vector<int> keep; for(int id:allowed[b]) {
     ++partial_checks; int r=execute(c,removed,retained,b?nullptr:&actions[id],b?&actions[id]:nullptr);
     if(r!=0)keep.push_back(id);
    }
    allowed[b].swap(keep);if(allowed[b].empty())break;
   }
   if(allowed[b].empty()){impossible=true;break;}
  }
  uint64_t recipes=0,certified=0;
  if(!impossible)for(int z:allowed[0])for(int o:allowed[1]) {
   ++recipes;bool ok=true;
   for(int b=0;b<2 && ok;++b)for(C& c:cs[b]) {
    if(c.keys.empty())c=condition(c.state,c.pattern,removed,retained);
    ++full_checks;if(execute(c,removed,retained,&actions[z],&actions[o])!=1){ok=false;break;}
   }
   if(ok){++certified; E a=actions[z],b=actions[o];certs<<removed<<'\t'<<retained<<'\t'<<a.w<<'\t'<<a.d<<'\t'<<a.t<<'\t'<<b.w<<'\t'<<b.d<<'\t'<<b.t<<'\n';}
  }
  ++pair_count;recipe_count+=recipes;cert_count+=certified;
  ledger<<removed<<'\t'<<retained<<'\t'<<allowed[0].size()<<'\t'<<allowed[1].size()<<'\t'<<recipes<<'\t'<<certified<<'\n';
  if(pair_count%1000==0){cerr<<"pairs "<<pair_count<<" full recipes "<<recipe_count<<" certificates "<<cert_count<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';ledger.flush();certs.flush();}
 }
 cout<<"{\"state_pairs\":"<<pair_count<<",\"actions_per_row\":"<<4*N<<",\"formal_recipe_domain\":"<<uint64_t(N)*(N-1)/2*(4*N)*(4*N)<<",\"partial_checks\":"<<partial_checks<<",\"full_recipes\":"<<recipe_count<<",\"full_context_checks\":"<<full_checks<<",\"certificates\":"<<cert_count<<",\"elapsed_seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<"}\n";
}
