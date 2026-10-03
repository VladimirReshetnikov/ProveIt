from fractions import Fraction as F
from math import factorial, log, lgamma
import json
from pathlib import Path
N=100
B=[[0]*(N+1) for _ in range(N+1)]
R=[[0]*(N+1) for _ in range(N+1)]
for n in range(N+1):
 B[n][0]=R[n][0]=1
 for m in range(1,n+1):
  lag=B[n-2][m-1] if n>=2 else (1 if (n,m)==(1,1) else 0)
  B[n][m]=2*B[n][m-1]+(m+1)*B[n-1][m]-m*lag
  R[n][m]=R[n][m-1]+(m+1)*R[n-1][m]
  assert 0<=B[n][m]<=2**m*R[n][m]
# Independent positive run-end recurrence; exceptional initial run has weight one.
A=[[0]*(N+1) for _ in range(N+1)]
for n in range(1,N+1): A[n][1]=1
for m in range(1,N):
 for n in range(m+1,N+1):
  def wt(k): return 2*(m+1)**k if k<2 else (2*(m+1)**2-(m+1))*(m+1)**(k-2)
  A[n][m+1]=sum(wt(k)*A[n-k][m] for k in range(n-m+1))
for n in range(1,N+1):
 for m in range(1,n+1):
  assert B[n][m]==sum((m+1)**k*A[n-k][m] for k in range(n-m+1))
# Signed normalized identity all reachable interior cells, including m=1 boundary.
def e(t,j):
 if t<0 or j<0 or j>t or (t+j)%2:return F(0)
 n,m=(t+j)//2,(t-j)//2
 return F(B[n][m],2**m*factorial(n)) if n<=N else None
checks=0
for n in range(2,N+1):
 for m in range(1,n+1):
  t,j=n+m,n-m
  rhs=F(t-j+2,t+j)*e(t-1,j-1)+e(t-1,j+1)-F(t-j,(t+j)*(t+j-2))*e(t-3,j-1)
  assert rhs==e(t,j),(n,m)
  checks+=1
prefix=[1,1,6,60,900,18480,487560,15824880,612504240,27619664640,1425084870240,82937356685760,5381249970008640,385518151040336640,30248651895457718400,2581418447382311243520,238181756821410417488640,23637327769847150582661120,2511570244361817605178754560,284573826857792109743033564160]
assert [B[n][n] for n in range(20)]==prefix
out={'max_n':N,'positive_renewal_cells':N*(N+1)//2,'normalized_recurrence_checks':checks,'oeis_terms_matched':20,'amplitude_ratios':{str(n):__import__('math').exp(log(B[n][n])-lgamma(n+1)-n*log(8)-3*(-2.338107410459767)*n**(1/3)-.875*log(n)) for n in [10,20,40,80,100]}}
Path(__file__).with_name('exact-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
