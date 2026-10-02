"""Independent exact coefficient and numerical sector audit."""
import sympy as s
import mpmath as mp
import json
from pathlib import Path
u=s.symbols('u')

def coefficients(M,sigma):
    mu=[s.Integer(1),s.Rational(sigma,2)]
    for j in range(2,3*M+1): mu.append(s.expand(sigma*mu[-1]/2+s.Rational(j-1,2)*mu[-2]))
    p=[s.Integer(0)]
    for h in range(1,M+1):
        q=(-1)**(h+1)*(u**(h+2)/s.Integer(h+2)+sigma*u**(h-1))
        if h>=2:q+=(-1)**(h+1)*s.Rational(h-1,2)*u**(h-2)
        p.append(q)
    b=[s.Integer(1)]
    for r in range(1,M+1): b.append(s.expand(sum(h*p[h]*b[r-h] for h in range(1,r+1))/s.Integer(r)))
    return [s.expand(sum(c*mu[e[0]] for e,c in s.Poly(v,u).terms())) for v in b]

def U(n,t):
    a,b=mp.mpf(1),t
    if n==0:return a
    for j in range(1,n):a,b=b,t*b-a
    return b

mp.mp.dps=90
norm=mp.sqrt(2*mp.pi)
def sector(n,sigma,scaled=False):
    r=(sigma+mp.sqrt(1+4*n))/2
    logL=mp.mpf(n)/2*(mp.log(n)-1)+sigma*mp.sqrt(n)-mp.mpf(5)/4-mp.log(2)/2 if scaled else 0
    f=lambda x:mp.exp(n*mp.log(x)-(x+1/x-sigma)**2/2-logL)/norm
    pts=sorted(set([mp.mpf(1),max(mp.mpf(1),r-12),max(mp.mpf(1),r),max(mp.mpf(1),r+12)]))+[mp.inf]
    return mp.quad(f,pts)

M=10
cp,cm=coefficients(M,1),coefficients(M,-1)
assert cm==[(-1)**r*x for r,x in enumerate(cp)]
assert cp[:3]==[1,s.Rational(31,24),-s.Rational(359,1152)]
I=[1,1]
for n in range(2,61): I.append(I[-1]+(n-1)*I[-2])
A=[sum((-1)**j*s.binomial(n-j,j)*I[n-2*j] for j in range(n//2+1)) for n in range(61)]
assert A[:8]==[1,1,1,2,5,13,37,112]
for n in range(4,61): assert A[n]==A[n-1]+(n-1)*A[n-2]-A[n-3]+A[n-4]
checks=[]
for n in [0,1,2,3,4,8,15,20]:
    central=mp.quad(lambda t:U(n,t)*mp.exp(-(t-1)**2/2)/norm,[-2,0,2])
    tails=[]
    for sig in [1,-1]:tails.append(mp.quad(lambda x:x**(-n-2)*mp.exp(-(x+1/x-sig)**2/2)/norm,[1,2,mp.inf]))
    rem=central-tails[0]-(-1)**n*tails[1]
    exact=sector(n,1)+(-1)**n*sector(n,-1)+rem
    error=abs(exact-int(A[n]))
    bound=n+1+2/(norm*(n+1))
    assert error<mp.mpf('1e-65') and abs(rem)<=bound
    checks.append(dict(n=n,identity_abs_error=str(error),R=str(rem),bound=str(bound)))
nums=[]
for n in [100,400,1600]:
  for sig in [1,-1]:
    exact=sector(n,sig,True)
    approx=sum(mp.mpf(str(c.p))/int(c.q)*sig**j/mp.sqrt(n)**j for j,c in enumerate(cp[:5]))
    nums.append(dict(n=n,sigma=sig,normalized_sector=str(exact),order4_residual=str(exact-approx),scaled_residual=str((exact-approx)*mp.sqrt(n)**5)))
data=dict(positive_coefficients=list(map(str,cp)),negative_coefficients=list(map(str,cm)),identity_checks=checks,sector_checks=nums)
Path('sector-checks.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
