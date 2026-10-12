#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using U=std::uint32_t;using W=std::uint64_t;
U modulus;U mul(U x,U y){return U(W(x)*y%modulus);}U add(U x,U y){W z=W(x)+y;return U(z>=modulus?z-modulus:z);}U sub(U x,U y){return x>=y?x-y:x+modulus-y;}
U power(U x,U n){U out=1;while(n){if(n&1)out=mul(out,x);x=mul(x,x);n>>=1;}return out;}
U determinant(std::vector<std::vector<U>> m){U out=1;int n=int(m.size());for(int col=0;col<n;++col){int pivot=col;while(pivot<n&&!m[pivot][col])++pivot;if(pivot==n)return 0;if(pivot!=col){std::swap(m[pivot],m[col]);out=modulus-out;}U value=m[col][col];out=mul(out,value);U inv=power(value,modulus-2);for(int row=col+1;row<n;++row){U factor=mul(m[row][col],inv);for(int k=col+1;k<n;++k)m[row][k]=sub(m[row][k],mul(factor,m[col][k]));}}return out;}
int main(int argc,char**argv){if(argc!=3)return 2;std::ifstream input(argv[1],std::ios::binary);char magic[4];U a,B,N;input.read(magic,4);input.read((char*)&modulus,4);input.read((char*)&a,4);input.read((char*)&B,4);input.read((char*)&N,4);if(std::string(magic,4)!="R14B"||a!=7||B!=80640||N!=2*B||modulus!=7340033)return 3;
 std::vector<U> bern(N+1);input.read((char*)bern.data(),4*(N+1));if(!input)return 4;char extra;if(input.read(&extra,1))return 5;
 U max=4*B+4*a;std::vector<U> f(max+1,1),fi(max+1,1),iv(max+1,1);for(U k=1;k<=max;++k)f[k]=mul(f[k-1],k);fi[max]=power(f[max],modulus-2);for(U k=max;k;--k)fi[k-1]=mul(fi[k],k);for(U k=1;k<=max;++k)iv[k]=mul(f[k-1],fi[k]);
 U choose[16][16]{};for(int h=0;h<16;++h){choose[h][0]=choose[h][h]=1;for(int j=1;j<h;++j)choose[h][j]=add(choose[h-1][j-1],choose[h-1][j]);}
 std::vector<U> residues;U zeros=0;
 for(U b=a+1;b<B;++b){std::vector<std::vector<U>> m(b<2*a?b:a,std::vector<U>(b<2*a?b:a));
  if(b<2*a){for(U t=0;t<b;++t)for(U k=0;k<b;++k){int j=int(t+k)-int(a)+1;if(j<0){m[t][k]=0;continue;}U mu=mul(bern[2*j],fi[2*j]);U bracket=mul(f[2*b+2*t-2*a+1],fi[2*b-2*k]);if(k<a)bracket=add(bracket,mul(f[2*t+1],fi[2*a-2*k]));m[t][k]=mul(mu,bracket);}}
  else {for(U i=0;i<a;++i){U n=b-a+i;std::vector<U> values(2*i+2),d(2*i+2);for(U y=0;y<values.size();++y){U v=2*n+2-y;for(U r=0;r<2*i;++r)v=mul(v,4*n+2-y-r);values[y]=v;}for(U h=0;h<d.size();++h){U v=0;for(U y=0;y<=h;++y){U term=mul(choose[h][y],values[y]);v=((h-y)&1)?sub(v,term):add(v,term);}d[h]=mul(v,fi[h]);}
   for(U ell=0;ell<a;++ell){U nn=2*(n-ell)+1,rr=2*b-2*a+2+2*ell;U F=mul(mul(mul(mul(f[2*n],fi[2*n-2*ell]),f[2*n+2*ell+2]),fi[2*n+2]),fi[2*ell+1]);U correction=0;for(U k=0;k<=i;++k){U fall=mul(f[nn],fi[nn-2*k-1]);U val=mul(mul(d[2*k+1],fall),mul(2,bern[2*b-2*(a-i+ell+k)]));correction=add(correction,val);}U scale=mul(mul(mul(mul(f[rr],fi[nn]),iv[2*n+1]),iv[2*n+2]),fi[2*ell+2]);m[i][ell]=add(add(F,F),mul(scale,correction));}}}
  U value=determinant(m);zeros+=value==0;residues.push_back(value);if(b%5000==0)std::cout<<"Native retained prefix "<<b<<" / "<<B-1<<" zeros "<<zeros<<std::endl;
 }
 std::ofstream out(argv[2],std::ios::binary);out.write("R14D",4);for(U value:{modulus,a,a+1,B-1,U(residues.size())})out.write((char*)&value,4);out.write((char*)residues.data(),4*residues.size());std::cout<<"Native complete cases "<<residues.size()<<" zeros "<<zeros<<std::endl;return zeros?1:0;}
