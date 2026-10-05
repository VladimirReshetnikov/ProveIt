#include <gmpxx.h>
#include <map>
#include <unordered_map>
#include <vector>
#include <array>
#include <iostream>
#include <cstdint>
#include <stdexcept>
using Key=uint64_t;
using Poly=std::unordered_map<Key,mpz_class>;
Key pack(const std::array<int,7>& v){Key k=0;for(int j=0;j<7;j++){if(v[j]<0||v[j]>31)throw std::runtime_error("exponent range");k|=Key(v[j])<<(5*j);}return k;}
void accumulate(Poly& a,const Poly& b,const mpz_class& scale=1){for(const auto& t:b){auto& c=a[t.first];c+=scale*t.second;if(c==0)a.erase(t.first);}}
Poly product(const Poly&a,const Poly&b){Poly c;for(const auto&x:a)for(const auto&y:b){Key k=x.first+y.first;auto&v=c[k];v+=x.second*y.second;if(v==0)c.erase(k);}return c;}
Poly read(){int n;std::cin>>n;Poly p;for(int i=0;i<n;i++){std::array<int,7> e;mpz_class c;for(auto&x:e)std::cin>>x;std::cin>>c;p[pack(e)]+=c;}return p;}
int main(){try{
 int n;std::cin>>n;std::vector<Poly> f(n);for(auto&v:f)v=read();
 auto var=[](int j){return Poly{{Key(1)<<(5*j),1}};};
 Poly a=var(0),b=var(1),c=var(2);accumulate(a,var(4));accumulate(b,var(5));accumulate(c,var(6));
 Poly twicep=product(a,b);for(auto&t:twicep)t.second*=2;
 accumulate(twicep,product(a,c),2);accumulate(twicep,product(b,c),2);accumulate(twicep,product(c,c));accumulate(twicep,c,-1);
 std::array<Poly,4> values{a,b,c,twicep};std::array<std::vector<Poly>,4> powers;
 for(auto&v:powers)v.push_back(Poly{{0,1}});
 int entries;std::cin>>entries;Poly answer;
 for(int z=0;z<entries;z++){
  int i,j,nt;std::cin>>i>>j>>nt;Poly coeff;
  for(int t=0;t<nt;t++){
   std::array<int,4> e;mpz_class v;for(auto&k:e)std::cin>>k;std::cin>>v;Poly term{{0,v}};
   for(int k=0;k<4;k++){while(int(powers[k].size())<=e[k])powers[k].push_back(product(powers[k].back(),values[k]));term=product(term,powers[k][e[k]]);}
   accumulate(coeff,term);
  }
  Poly summand=product(product(f[i],f[j]),coeff);accumulate(answer,summand,(i==j?1:2));
 }
 std::map<Key,mpz_class> sorted(answer.begin(),answer.end());std::cout<<sorted.size()<<"\n";
 for(const auto&t:sorted){for(int j=0;j<7;j++)std::cout<<((t.first>>(5*j))&31)<<" ";std::cout<<t.second<<"\n";}
}catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}}
