// Native finite-field elimination for exact, denominator-cleared search inputs.
// Modular membership is diagnostic until an independent rational certificate closes.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
using U=std::uint32_t; using I=std::int64_t;
template<U P> inline U mul(U a,U b){
 std::uint64_t z=std::uint64_t(a)*b;
 if constexpr(P==2147483647u){z=(z&P)+(z>>31);if(z>=P)z-=P;return U(z);}
 else return U(z%P);
}
template<U P> inline U sub(U a,U b){return a>=b?a-b:a+P-b;}
template<U P> U power(U a,U n){U r=1;while(n){if(n&1)r=mul<P>(r,a);a=mul<P>(a,a);n>>=1;}return r;}
struct Basis {std::vector<U> v;std::vector<std::pair<U,U>> deps;U scale,row,pivot;};
template<class T> void read(std::istream& in,T& x){in.read(reinterpret_cast<char*>(&x),sizeof(x));if(!in)throw std::runtime_error("Truncated matrix");}
template<U P> int solve(const std::string& filename,const std::string& output){
 auto start=std::chrono::steady_clock::now();std::ifstream in(filename,std::ios::binary);if(!in)throw std::runtime_error("Matrix missing");
 char magic[4];in.read(magic,4);if(std::string(magic,4)!="S6M1")throw std::runtime_error("Bad matrix format");U nr,nc;std::uint64_t denominator;read(in,nr);read(in,nc);read(in,denominator);
 if(!nr||nr>20000||!nc||nc>20000)throw std::runtime_error("Unexpected matrix dimensions");
 std::vector<int> piv(nc,-1);std::vector<Basis> basis;std::vector<I> raw(nc);std::vector<U> q(nc);
 auto load=[&](){in.read(reinterpret_cast<char*>(raw.data()),nc*sizeof(I));if(!in)throw std::runtime_error("Truncated row");for(U j=0;j<nc;++j){I z=raw[j]%I(P);if(z<0)z+=P;q[j]=U(z);}};
 for(U row=0;row<nr;++row){
  load();std::vector<std::pair<U,U>> deps;
  for(U col=0;col<nc;++col){if(!q[col])continue;U a=q[col];int bi=piv[col];
   if(bi>=0){auto& b=basis[bi];deps.emplace_back(U(bi),a);for(U j=col;j<nc;++j)q[j]=sub<P>(q[j],mul<P>(a,b.v[j]));}
   else {U scale=power<P>(a,P-2);for(U j=col;j<nc;++j)q[j]=mul<P>(q[j],scale);piv[col]=int(basis.size());basis.push_back(Basis{q,std::move(deps),scale,row,col});break;}
  }
  if((row+1)%500==0)std::cout<<"Native rows "<<row+1<<" / "<<nr<<" rank "<<basis.size()<<std::endl;
 }
 load();std::vector<U> weights(basis.size(),0);bool member=true;
 for(U col=0;col<nc;++col){if(!q[col])continue;int bi=piv[col];if(bi<0){member=false;break;}U a=q[col];weights[bi]=a;auto& b=basis[bi];for(U j=col;j<nc;++j)q[j]=sub<P>(q[j],mul<P>(a,b.v[j]));}
 U residual=U(std::count_if(q.begin(),q.end(),[](U x){return x!=0;}));std::vector<U> coefficients(nr,0);bool verified=false;
 if(member){
  for(std::size_t i=basis.size();i-->0;){U c=mul<P>(weights[i],basis[i].scale);coefficients[basis[i].row]=c;for(auto [j,a]:basis[i].deps)weights[j]=sub<P>(weights[j],mul<P>(c,a));}
  in.clear();in.seekg(20);std::vector<U> check(nc,0);
  for(U row=0;row<nr;++row){load();U c=coefficients[row];if(!c)continue;for(U j=0;j<nc;++j){U z=mul<P>(c,q[j]);check[j]=sub<P>(check[j],P-z);}}
  load();verified=check==q;if(!verified)throw std::runtime_error("Back-substitution verification failed");
 }
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::ofstream out(output);out<<"{\n\"status\":\"SEARCH_DIAGNOSTIC\",\n\"prime\":"<<P<<",\n\"rows\":"<<nr<<",\n\"columns\":"<<nc<<",\n\"common_denominator\":"<<denominator<<",\n\"rank\":"<<basis.size()<<",\n\"target_modular_member\":"<<(member?"true":"false")<<",\n\"target_modular_residual_terms\":"<<residual<<",\n\"solution_verified\":"<<(verified?"true":"false")<<",\n\"elapsed_seconds\":"<<seconds<<",\n\"selected_row_indices\":[";
 for(std::size_t i=0;i<basis.size();++i){if(i)out<<',';out<<basis[i].row;}out<<"],\n\"pivot_columns\":[";for(std::size_t i=0;i<basis.size();++i){if(i)out<<',';out<<basis[i].pivot;}out<<"],\n\"coefficients\":[";for(U i=0;i<nr;++i){if(i)out<<',';out<<coefficients[i];}out<<"],\n\"scope\":\"Native modular search on exact denominator-cleared projected rows. Neither modular membership nor nonmembership is an exact rational period certificate.\"\n}\n";
 std::cout<<"Native final rank "<<basis.size()<<" target member "<<member<<" verified "<<verified<<" seconds "<<seconds<<std::endl;return 0;
}
int main(int argc,char** argv){try{if(argc!=3){std::cerr<<"matrix.bin receipt.json required\n";return 2;}return solve<2147483647u>(argv[1],argv[2]);}catch(const std::exception& e){std::cerr<<e.what()<<std::endl;return 1;}}
