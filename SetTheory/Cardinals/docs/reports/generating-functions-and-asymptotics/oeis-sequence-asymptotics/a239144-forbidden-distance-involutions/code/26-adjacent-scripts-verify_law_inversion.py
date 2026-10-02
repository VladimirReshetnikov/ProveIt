"""Independent numerical checks of law/TV and Newton inversion; not proof authority."""
import json,math
from pathlib import Path
import mpmath as mp
import sympy as S
mp.mp.dps=110
D=json.loads(Path('involution-coefficients.json').read_text())
def rr(x):
 p,q=S.fraction(S.sympify(x));return mp.mpf(str(p))/mp.mpf(str(q))
V=list(map(rr,D['total_variation']));beta=list(map(rr,D['avoidance_log']))
I=[1,1];A=[1,1,1,2]
for n in range(2,20001):I.append(I[-1]+(n-1)*I[-2])
for n in range(4,20001):A.append(A[-1]+(n-1)*A[-2]-A[-3]+A[-4])
rows=[]
for n in [100,1000,5000,20000]:
 t=1/mp.sqrt(n);K=min(n//2,90)
 moments=[mp.mpf(math.comb(n-k,k))*I[n-2*k]/I[n] for k in range(K+1)]
 probs=[sum((-1)**(k-l)*math.comb(k,l)*moments[k] for k in range(l,K+1)) for l in range(K+1)]
 tv=mp.fsum(abs(p-mp.exp(-1)/mp.factorial(l)) for l,p in enumerate(probs))/2
 row={'n':n,'TV':str(tv),'TV_scaled_cubic_residual':str((mp.e*tv-t+t*t/2)/t**3),'TV_scaled_order8_residual':str((mp.e*tv-sum(V[j]*t**j for j in range(1,8)))/t**8),'inversion':{}}
 for J in [3,7]:
  b=mp.log(A[n]);x=2*b/mp.lambertw(2*b/mp.e);x0=x
  def L(x):return x*(mp.log(x)-1)/2+mp.sqrt(x)-mp.log(2)/2-mp.mpf(5)/4+sum(beta[j]*x**(-mp.mpf(j)/2) for j in range(1,J+1))
  def Lp(x):return mp.log(x)/2+1/(2*mp.sqrt(x))-sum(mp.mpf(j)/2*beta[j]*x**(-mp.mpf(j)/2-1) for j in range(1,J+1))
  steps=math.ceil(math.log2(J+3))
  for step in range(steps):x-=(L(x)-b)/Lp(x)
  row['inversion'][str(J)]={'steps':steps,'x_minus_n':str(x-n),'scaled_error':str((x-n)*n**(mp.mpf(J+1)/2)*mp.log(n))}
 rows.append(row)
Path('law-inversion-checks.json').write_text(json.dumps({'purpose':'Numerical sanity checks; exact signed moments truncated at K<=90. Tail l1 bound is sum_(k>K)2^k/k!, negligible at displayed precision for large n.','TV_next_coefficient':D['total_variation'][8],'rows':rows},indent=2)+'\n')
for r in rows:print(r['n'],'TV cubic',r['TV_scaled_cubic_residual'][:25],'inverse3',r['inversion']['3']['scaled_error'][:25],'inverse7',r['inversion']['7']['scaled_error'][:25])
