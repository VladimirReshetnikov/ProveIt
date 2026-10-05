#include <gmpxx.h>
#include <unordered_map>
#include <vector>
#include <iostream>
#include <algorithm>
#include <cstdint>
using P=std::unordered_map<uint64_t,mpz_class>;
void clean(P& p){for(auto it=p.begin();it!=p.end();)if(it->second==0)it=p.erase(it);else ++it;}
P add(P a,const P& b){for(auto& [k,v]:b)a[k]+=v;clean(a);return a;}
P mul(const P& a,const P& b){P out;if(a.empty()||b.empty())return out;out.reserve(std::min<size_t>(a.size()*b.size(),500000));for(auto& [i,v]:a)for(auto& [j,w]:b)out[i+j]+=v*w;clean(out);return out;}
P scale(P a,const mpz_class& c){for(auto& [k,v]:a)v*=c;clean(a);return a;}
P readpoly(){size_t n;std::cin>>n;P p;for(size_t k=0;k<n;k++){uint64_t e;mpz_class c;std::cin>>e>>c;p[e]=c;}return p;}
int main(){int nv,np;std::cin>>nv>>np;std::vector<P> vec;for(int i=0;i<nv;i++)vec.push_back(readpoly());
P aa={{1,1},{1ULL<<24,1}},bb={{1ULL<<6,1},{1ULL<<30,1}},cc={{1ULL<<12,1},{1ULL<<36,1}};
P pp=add(add(scale(mul(aa,bb),2),scale(mul(aa,cc),2)),scale(mul(bb,cc),2));pp=add(pp,add(mul(cc,cc),scale(cc,-1)));
std::vector<P> vals={aa,bb,cc,pp};std::vector<std::vector<P>> powers(4);for(int j=0;j<4;j++)powers[j].push_back(P{{0,1}});
P out;
for(int z=0;z<np;z++){int i,j;size_t n;std::cin>>i>>j>>n;P cp;
for(size_t k=0;k<n;k++){int e[4];mpz_class coeff;std::cin>>e[0]>>e[1]>>e[2]>>e[3]>>coeff;P term{{0,coeff}};for(int h=0;h<4;h++){while((int)powers[h].size()<=e[h])powers[h].push_back(mul(powers[h].back(),vals[h]));term=mul(term,powers[h][e[h]]);}cp=add(std::move(cp),term);}
P prod=mul(vec[i],vec[j]);prod=mul(cp,prod);if(i!=j)prod=scale(std::move(prod),2);out=add(std::move(out),prod);std::cerr<<"entry "<<z+1<<"/"<<np<<" terms "<<out.size()<<"\n";
}
std::vector<uint64_t> keys;for(auto& [k,v]:out)keys.push_back(k);std::sort(keys.begin(),keys.end());std::cout<<keys.size()<<"\n";for(auto k:keys)std::cout<<k<<" "<<out[k]<<"\n";
}
