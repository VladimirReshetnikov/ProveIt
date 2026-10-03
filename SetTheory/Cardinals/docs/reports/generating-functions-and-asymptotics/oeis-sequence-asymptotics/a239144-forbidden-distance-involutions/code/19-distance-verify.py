# Exact coefficient generation and frontier matching verification.
import sympy as S, json, mpmath as mp
from collections import defaultdict
from pathlib import Path
import os
OUT=Path(os.environ.get("OUTPUT_DIR", Path(__file__).resolve().parents[1]/"results")).resolve()
OUT.mkdir(parents=True, exist_ok=True)
u,t,w=S.symbols('u t w'); a=S.symbols('a1:5'); J=6
mom=[S.Integer(1),S.Rational(1,2)]
for k in range(2,3*J+1):mom.append(mom[-1]/2+S.Rational(k-1,2)*mom[-2])
def expect(p):
 p=S.Poly(S.expand(p),u); return S.expand(sum(c*mom[k[0]] for k,c in p.terms()))
p=[]
for h in range(1,J+1):
 q=(-1)**(h+1)*u**(h+2)/S.Integer(h+2)
 for j in range(1,min(len(a),(h+2)//2)+1):
  k=h-(2*j-2)
  if k>=0:q-=a[j-1]*(-1)**k*S.binomial(2*j+k-1,k)*u**k
 p.append(S.expand(q))
b=[S.Integer(1)]
for r in range(1,J+1):b.append(S.expand(sum(h*p[h-1]*b[r-h] for h in range(1,r+1))/r))
d=[expect(x) for x in b]; A=[x.subs(dict.fromkeys(a,0)) for x in d]
Ds=[S.expand(x.subs({a[j]:(-1)**(j+1)*a[j]*w**(j+1) for j in range(len(a))},simultaneous=True)) for x in d]
P=[S.Integer(1)]
for r in range(1,J+1):P.append(S.expand(Ds[r]-sum(A[k]*P[r-k] for k in range(1,r+1))))
(OUT/'coefficients.json').write_text(json.dumps({'sector':[str(x) for x in d],'pgf':[str(x) for x in P]},indent=2))
assert P[1]==-a[0]*w
assert S.expand(P[2]-(S.Rational(3,2)*a[0]*w+(S.Rational(3,2)*a[0]**2-a[1])*w*w))==0
# Matching counts for graph forbidding distances 1..r, independently by frontier DP.
def counts(n,r):
 states={(0,0):1}
 for i in range(n):
  nxt=defaultdict(int)
  for (mask,k),val in states.items():
   nxt[(mask>>1,k)]+=val
   if not mask&1:
    for dist in range(1,min(r,n-1-i)+1):
     if not mask>>dist&1:nxt[((mask|1<<dist)>>1,k+1)]+=val
  states=nxt
 return [states.get((0,k),0) for k in range(n//2+1)]
def stats(M,n):
 # log sum M_k z^k, compute coefficients by logarithmic derivative
 z=S.symbols('z'); c=[S.Rational(0)]
 for j in range(1,len(a)+1):
  v=(j*M[j] if j<len(M) else 0)-sum(k*c[k]*(M[j-k] if j-k<len(M) else 0) for k in range(1,j))
  c.append(S.Rational(v,j))
 return [(-1)**(j+1)*c[j]/n for j in range(1,len(a)+1)]
mp.mp.dps=70
I=[1,1]
for n in range(2,501):I.append(I[-1]+(n-1)*I[-2])
rows=[]
for r in [1,2,3]:
 for n in [40,100,250,500]:
  M=counts(n,r); av=stats(M,n); exact=mp.mpf(sum((-1)**k*x*I[n-2*k] for k,x in enumerate(M)))/I[n]
  vals=[mp.mpf(str(S.N(x.subs(dict(zip(a,av))).subs(w,-1),75))) for x in P]
  approx=mp.exp(-mp.mpf(str(av[0])))*sum(vals[j]*mp.mpf(n)**(-mp.mpf(j)/2) for j in range(J+1))
  rows.append({'r':r,'n':n,'exact':str(exact),'error_order6':str(exact-approx),'scaled_error':str((exact-approx)*mp.mpf(n)**S.Rational(7,2))})
(OUT/'numeric-checks.json').write_text(json.dumps(rows,indent=2));print('\n'.join(str(x) for x in rows));print('D3=',d[3]);print('P3=',P[3])
