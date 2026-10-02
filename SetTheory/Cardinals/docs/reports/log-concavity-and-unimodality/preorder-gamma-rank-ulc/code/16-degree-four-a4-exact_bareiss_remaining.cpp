#include <gmpxx.h>
#include <iostream>
#include <vector>
#include <stdexcept>
using namespace std;
int main(){
 int m,n; if(!(cin>>m>>n)) return 2;
 vector<vector<mpz_class>> a(m,vector<mpz_class>(n+1));
 for(auto &r:a) for(auto &v:r) cin>>v;
 mpz_class prev=1,t,u;
 for(int k=0;k<n;k++) {
  int p=k; while(p<m&&a[p][k]==0)p++;
  if(p==m){cerr<<"rank deficient at "<<k<<endl;return 3;}
  if(p!=k) swap(a[p],a[k]);
  mpz_class pivot=a[k][k];
  for(int i=k+1;i<m;i++){
   mpz_class c=a[i][k];
   for(int j=k+1;j<=n;j++){
    t=a[i][j]*pivot-c*a[k][j];
    if(prev!=1){if(!mpz_divisible_p(t.get_mpz_t(),prev.get_mpz_t())){cerr<<"non-exact division"<<endl;return 4;}mpz_divexact(t.get_mpz_t(),t.get_mpz_t(),prev.get_mpz_t());}
    a[i][j]=t;
   }
   a[i][k]=0;
  }
  prev=pivot;
 }
 for(int i=n;i<m;i++)if(a[i][n]!=0){cerr<<"inconsistent"<<endl;return 5;}
 vector<mpq_class> x(n);
 for(int i=n-1;i>=0;i--){mpq_class b(a[i][n]);for(int j=i+1;j<n;j++)b-=mpq_class(a[i][j])*x[j];x[i]=b/mpq_class(a[i][i]);x[i].canonicalize();}
 for(auto&v:x)cout<<v<<'\n';
}
