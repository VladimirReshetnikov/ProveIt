#include <bits/stdc++.h>
namespace audit {
#define main audit_original_main
#include "audit_census.cpp"
#undef main
}
namespace cutoff {
#define main cutoff_original_main
#include "producer/census.cpp"
#undef main
}
namespace weighted {
#define main weighted_original_main
#include "producer/census_graph.cpp"
#undef main
}
int main(int argc,char**argv){
 int n=argc>1?atoi(argv[1]):3,Q=1<<n,M=1<<(n*n);
 audit::n=cutoff::n=weighted::n=n;audit::q=cutoff::Q=weighted::Q=Q;audit::m=cutoff::M=weighted::M=M;
 audit::fw.assign(M,std::vector<int>(Q));audit::backward=audit::fw;
 for(int C=0;C<M;++C)for(int z=0;z<Q;++z)for(int u=0;u<n;++u)for(int v=0;v<n;++v)if(C&(1<<(n*u+v))){if(z&(1<<u))audit::fw[C][z]|=1<<v;if(z&(1<<v))audit::backward[C][z]|=1<<u;}
 cutoff::im=weighted::im=audit::fw;cutoff::rev.resize(M);weighted::rev.resize(M);
 for(int C=0;C<M;++C){int D=0;for(int u=0;u<n;++u)for(int v=0;v<n;++v)if(C>>(u*n+v)&1)D|=1<<(v*n+u);cutoff::rev[C]=weighted::rev[C]=D;}
 std::vector<audit::Orbit> orbits(M*Q*Q);for(int E=0;E<M;++E)for(int I=1;I<Q;++I)for(int F=1;F<Q;++F)orbits[(E*Q+I)*Q+F]=audit::make_orbit(E,I,F);
 long long checked=0,expanded=0;
 for(int A=0;A<M;++A)for(int B=0;B<M;++B)for(int I=1;I<Q;++I)for(int F=1;F<Q;++F){
  const auto&o=orbits[((A|B)*Q+I)*Q+F];int a=audit::evaluate(A,B,I,F,o);int b=cutoff::solve(A,B,I,F).rank;int c=weighted::solve(A,B,I,F).rank;
  if(a!=b||a!=c){std::cerr<<"Mismatch "<<A<<" "<<B<<" "<<I<<" "<<F<<" : "<<a<<" "<<b<<" "<<c<<"\n";return 1;}
  if(checked%997==0){auto z=o;z.t=o.t+1;z.p=2*o.p;z.P.clear();z.R.clear();for(int k=0;k<z.t+z.p;++k){z.P.push_back(o.pf(k));z.R.push_back(o.rb(k));}int d=audit::evaluate(A,B,I,F,z);assert(d==a);++expanded;}
  ++checked;
 }
 std::cout<<"{\"states\":"<<n<<",\"pointwise_three_algorithm_comparisons\":"<<checked<<",\"nonminimal_period_and_transient_checks\":"<<expanded<<",\"passed\":true}\n";
}
