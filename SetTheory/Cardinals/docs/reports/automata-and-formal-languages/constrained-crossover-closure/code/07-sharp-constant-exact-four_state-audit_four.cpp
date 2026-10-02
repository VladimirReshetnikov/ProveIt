#include <bits/stdc++.h>
#define main census_original_main
#include "../audit_census.cpp"
#undef main
struct IF{int I,F;Orbit o;};
struct Work{int E;vector<IF> pairs;};
Orbit floyd_orbit(int E,int I,int F){
 auto next=[&](int z){return fw[E][z/q]*q+backward[E][z%q];};
 int start=I*q+F,a=next(start),b=next(next(start));while(a!=b){a=next(a);b=next(next(b));}
 int t=0;a=start;while(a!=b){a=next(a);b=next(b);++t;}
 int p=1;b=next(a);while(a!=b){b=next(b);++p;}
 Orbit o;o.t=t;o.p=p;int z=start;for(int k=0;k<t+p;++k){o.P.push_back(z/q);o.R.push_back(z%q);z=next(z);}return o;
}
bool universal_interior(int A,int B,int F,const Orbit&o){
 for(int r=0;r<o.p;++r){if(!(o.ps(r)&F))continue;vector<int>S(o.p);for(int a=0;a<o.p;++a)S[a]=o.ps(a)&o.rs(r-a);
  vector<char>seen(o.p*q);vector<int>work={o.t%o.p*q+S[o.t%o.p]};seen[work[0]]=true;
  for(size_t k=0;k<work.size();++k){int a=work[k]/q,Z=work[k]%q,b=(a+1)%o.p;
   for(int C:{A,B})if(fw[C][S[a]]&S[b]){int T=fw[C][Z]&S[b];if(!T)return false;int v=b*q+T;if(!seen[v]){seen[v]=true;work.push_back(v);}}
  }
 }
 return true;
}
int main(){
 n=4;q=16;m=65536;fw.assign(m,vector<int>(q));backward=fw;
 for(int C=0;C<m;++C)for(int u=0;u<n;++u)for(int v=0;v<n;++v)if(C&(1<<(n*u+v)))for(int z=1;z<q;++z){if(z&(1<<u))fw[C][z]|=1<<v;if(z&(1<<v))backward[C][z]|=1<<u;}
 vector<array<int,4>> perms;array<int,4>p={0,1,2,3};do{perms.push_back(p);}while(next_permutation(p.begin(),p.end()));
 vector<char> covered(m);vector<Work>all;long long raw=0,canonical_graphs=0,npairs=0;int max_t=0,max_p=0,max_H=0;
 ofstream list("independent-high-transient-pairs.txt");
 for(int E=0;E<m;++E){if(covered[E])continue;++canonical_graphs;
  for(auto pi:perms){int image=0;for(int u=0;u<n;++u)for(int v=0;v<n;++v)if(E&(1<<(n*u+v)))image|=1<<(n*pi[u]+pi[v]);covered[image]=true;}
  Work w;w.E=E;
  for(int I=1;I<q;++I)for(int F=1;F<q;++F){auto o=floyd_orbit(E,I,F);max_t=max(max_t,o.t);max_p=max(max_p,o.p);max_H=max(max_H,2*o.t+o.p*(q-1)-1);if(o.t>=4){list<<E<<" "<<I<<" "<<F<<" "<<o.t<<"\n";w.pairs.push_back({I,F,o});}}
  if(!w.pairs.empty()){long long labels=1;for(int k=0;k<__builtin_popcount((unsigned)E);++k)labels*=3;raw+=labels*w.pairs.size();npairs+=w.pairs.size();all.push_back(move(w));}
 }
 list.close();cout<<"CANDIDATES canonical_underlying_graphs "<<canonical_graphs<<" retained_graphs "<<all.size()<<" pairs "<<npairs<<" raw_label_budget "<<raw<<" label_quotient_budget "<<(raw+npairs)/2<<" max_t "<<max_t<<" max_p "<<max_p<<" max_H "<<max_H<<endl;
 long long tested=0,sampled_unbounded=0;map<int,long long>counts;int best=0,done=0;
 for(const Work&w:all){vector<int>bits;for(int b=15;b>=0;--b)if(w.E>>b&1)bits.push_back(1<<b);
  function<void(int,int,int,bool)> enumerate=[&](int k,int A,int B,bool distinct){
   if(k==(int)bits.size()){
    assert(A<=B && (A|B)==w.E);
    for(const IF&pair:w.pairs){bool finite=universal_interior(A,B,pair.F,pair.o);int value=-1;
     if(finite)value=evaluate(A,B,pair.I,pair.F,pair.o);
     else if(tested%997==0){assert(evaluate(A,B,pair.I,pair.F,pair.o)==-1);++sampled_unbounded;}
     assert(!finite || value>=0);++tested;++counts[value];if(value>best){best=value;cout<<"BEST "<<best<<" E "<<w.E<<" A "<<A<<" B "<<B<<" I "<<pair.I<<" F "<<pair.F<<" tested "<<tested<<endl;}
    }
    return;
   }
   int bit=bits[k];enumerate(k+1,A|bit,B|bit,distinct); // both labels
   enumerate(k+1,A,B|bit,true); // first unequal bit must be B-only
   if(distinct)enumerate(k+1,A|bit,B,true);
  };
  enumerate(0,0,0,false);if(++done%25==0)cout<<"PROGRESS graphs "<<done<<" tested "<<tested<<" best "<<best<<endl;
 }
 assert(tested==(raw+npairs)/2);cout<<"DONE graphs "<<done<<" tested "<<tested<<" best "<<best<<" sampled_unbounded_graph_checks "<<sampled_unbounded<<endl;
 for(auto[r,c]:counts)cout<<"RANK "<<r<<" COUNT "<<c<<endl;
}
