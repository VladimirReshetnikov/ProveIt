from pathlib import Path
SCRIPT_DIR = Path(__file__).resolve().parent
RESULT_DIR = SCRIPT_DIR.parent / "results"
RESULT_DIR.mkdir(exist_ok=True)
"""Finite half-power generator from the exact log-GF; no fitted coefficients."""
import contextlib,io,runpy,math,json
from collections import defaultdict
import mpmath as mp
with contextlib.redirect_stdout(io.StringIO()): data=runpy.run_path(str(SCRIPT_DIR / 'check_scores.py'))
mp.mp.dps=60
mu=data['mu'];lam=data['lam'];N=data['N'];p=1-mp.exp(-lam);c=mp.exp(-lam)*mu
M=4
# Exact-integer subtraction for the analytic divisor remainder.
r=[mp.mpf(0)]+[mp.mpf(2*j*N[j]-math.comb(2*j,j))/(2*j*j) for j in range(1,250)]
e={}
for j in range(1,(M+2)//2+1):
 e[j]=-mp.log(2)/j-mp.harmonic(j-1)/(2*j)+(-1)**j*sum(r[n]*mp.mpf(math.factorial(n)//math.factorial(n-j))/mp.mpf(4)**n for n in range(j,250))/mp.factorial(j)
X=[mp.mpf(0)]*(M+3)
for j in range(2,M+3):
 if j%2==0:X[j]=-e[j//2]
 else:X[j]=-mp.mpf(2)/j*sum(mp.mpf(1)/(2*k+1) for k in range((j-1)//2))
g=[mp.mpf(1)]
for m in range(1,M+3):g.append(sum(j*X[j]*g[m-j] for j in range(1,m+1))/m)
d={j:g[j]/mu for j in range(2,M+3)}
# Monomials are s^(a/2)/(s+tau)^b.
def mul(A,B):
 out=defaultdict(mp.mpf)
 for (a,b),v in A.items():
  for (aa,bb),vv in B.items():out[(a+aa,b+bb)]+=v*vv
 return dict(out)
def add(*polys):
 out=defaultdict(mp.mpf)
 for poly in polys:
  for k,v in poly.items():out[k]+=v
 return dict(out)
R=[{(0,1):mp.mpf(1)}]
for m in range(1,M+1):R.append(add(*(mul({(j+2,1):-d[j+2]},R[m-j]) for j in range(1,m+1))))
K=[{(0,0):mp.mpf(1)}]
for m in range(1,M+1):
 terms=[]
 for j in range(2,m+1,2):
  z=j//2
  L={(2*z,0):mp.mpf(j)/(m*z),(2*z+2,0):mp.mpf(j)/(m*(z+1))}
  terms.append(mul(L,K[m-j]))
 K.append(add(*terms))
polys=[add(*(mul(K[j],R[m-j]) for j in range(m+1))) for m in range(M+1)]
def kernel(a,b,tau):
 if a%2==0:
  aa=a//2
  return mp.exp(-tau)*sum(mp.binomial(aa,j)*(-tau)**j/mp.factorial(b-aa+j-1) for j in range(aa+1) if b-aa+j>=1)
 alpha=mp.mpf(a)/2
 return mp.hyp1f1(b,b-alpha,-tau)/mp.gamma(b-alpha)
def coefficients(tau):return [sum(v*kernel(a,b,tau) for (a,b),v in poly.items()) for poly in polys]
if __name__=='__main__':
 rows=json.load(open(str(RESULT_DIR / 'crossover-checks.json')))['checks']
 for row in rows:
  n=row['n'];tau=mp.mpf(row['tau']);a=mp.mpf(n)*c/(n*p+tau*c)
  cc=coefficients(tau)
  for m in [2,3,4]:
   model=sum(cc[j]/mp.mpf(n)**(mp.mpf(j)/2) for j in range(m+1))/a
   row[f'M{m}_model']=float(model)
   row[f'M{m}_scaled_residual']=float(mp.mpf(n)**(mp.mpf(m+1)/2)*(mp.mpf(row['actual'])-model))
  print(n,round(float(tau),3),*[row[f'M{m}_scaled_residual'] for m in [2,3,4]])
 out={'d':{str(k):str(v) for k,v in d.items()},'kernels':[{str(k):str(v) for k,v in poly.items()} for poly in polys],'checks':rows}
 open(str(RESULT_DIR / 'allorders-crossover-checks.json'),'w').write(json.dumps(out,indent=2))
