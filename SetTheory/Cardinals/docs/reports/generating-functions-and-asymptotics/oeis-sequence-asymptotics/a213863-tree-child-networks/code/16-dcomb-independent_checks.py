from fractions import Fraction as F
from math import comb, factorial, prod
from pathlib import Path
import json
out=[]
for d in range(2,13):
    b={1:{1:1}}; a=[1]
    for n in range(1,21):
        if n>1:
            b[n]={m:comb(d*n+m-2,d-1)*sum(b[n-1].get(j,0) for j in range(1,m+1)) for m in range(1,n+1)}
        a.append(sum(b[n].values()))
    # Compute D directly, never using the A update.
    L=F((d+1)**(d-1),factorial(d-1))
    def D(N,j):
        if j<0 or j>N or (N+j)%2: return F(0)
        n,k=(N+j)//2,(N-j)//2
        if not n: return F(1)
        return F(sum(b[n].get(m,0) for m in range(1,k+2)),L**n*factorial(n)**(d-1))
    def p(N,j): return prod(1-F(2*(j+h),(d+1)*(N+j)) for h in range(1,d))
    checks=0
    for N in range(1,21):
        for j in range(N%2,N+1,2):
            assert D(N,j)==D(N-1,j+1)+(p(N,j)*D(N-1,j-1) if j else 0)
            checks+=1
    for N in range(1,21):
        for j in range(1,N+2):
            for h in range(1,d): assert F(1,d+1)<=1-F(2*(j+h),(d+1)*(N+j))<1
            assert p(N+1,j)>p(N,j)
    c=F(2*(d-1),d+1); kap=F((d-1)*(d-2),d+1); eta=F((d-1)**2,2*(d+1))
    assert c/2+kap==2*eta
    assert -kap/2-c/4-F(1,6)==-eta-F(1,6)
    alpha=-F(d*(3*d-1),2*(d+1));rho=-eta-F(1,2)
    assert alpha+d-1==rho
    out.append(dict(d=d,diagonal=a[:8],normalized_checks=checks,positive_monotone=True,exponent_shift=True))
Path(__file__).with_name('independent_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS independent source-array normalization, all physical boundaries, positivity, monotonicity, drift constants and leaf exponents for d=2,...,12')
