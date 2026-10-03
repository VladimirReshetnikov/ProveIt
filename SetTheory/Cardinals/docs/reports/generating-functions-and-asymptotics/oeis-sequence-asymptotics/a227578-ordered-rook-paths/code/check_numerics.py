from functools import lru_cache
from math import factorial,prod
import mpmath as mp,json,time
mp.mp.dps=65
@lru_cache(None)
def rook(l):
 if not any(l):return 1
 return sum(rook(l[:i]+(j,)+l[i+1:]) for i,x in enumerate(l) for j in range(l[i-1] if i else 0,x))
rows=[]
for k,ns in [(2,[25,50,100]),(3,[20,40,80]),(4,[10,20,30]),(5,[5,10,15])]:
 for n in ns:
  a=rook((n,)*k);alpha=mp.mpf(k*k-1)/2
  C=mp.mpf(prod(factorial(j) for j in range(k)))*mp.mpf(k)**(-mp.mpf(k*k)/2+k+1)*mp.mpf(k+1)**(k*k-k-1)/((2*mp.pi)**(mp.mpf(k-1)/2)*mp.mpf(k+2)**alpha)
  d1=-mp.mpf((k-1)*(k+1)*(2*k**4+8*k**3+9*k*k+6*k+12))/(12*k*(k+2)**2)
  rat=mp.mpf(a)*mp.mpf(n)**alpha/(C*mp.mpf(k+1)**(k*n))
  rows.append(dict(k=k,n=n,exact_count=str(a),normalized_count=str(rat),leading_relative_error=str(1/rat-1),one_correction_relative_error=str((1+d1/n)/rat-1),n2_scaled_normalized_residual=str(n*n*(rat-1-d1/n))))
  print(k,n,mp.nstr(rat,14),flush=True)
 rook.cache_clear()
json.dump(rows,open('direct-numerics.json','w'),indent=2)
