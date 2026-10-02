#!/usr/bin/env python3
"""Exact corroboration of the ordinary A022629 proof; not an analytic proof."""
import sys
if not __debug__:
    raise SystemExit('Assertions must be enabled; do not use -O.')
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import argparse, hashlib, json
p=argparse.ArgumentParser(); p.add_argument('--output-dir',default=str(Path(__file__).parent)); args=p.parse_args()
out=Path(args.output_dir); out.mkdir(parents=True,exist_ok=True)
N=250
# Independent finite-product dynamic program and logarithmic derivative recurrence.
a=[0]*(N+1); a[0]=1
for k in range(1,N+1):
    for n in range(N,k-1,-1): a[n]+=k*a[n-k]
b=[0]*(N+1)
for k in range(1,N+1):
    for j in range(1,N//k+1): b[k*j]+=(-1)**(j+1)*k**(j+1)
c=[0]*(N+1); c[0]=1
for n in range(1,N+1):
    v=sum(b[j]*c[n-j] for j in range(1,n+1)); assert v%n==0; c[n]=v//n
assert a==c
assert a[:15]==[1,1,2,5,7,15,25,43,64,120,186,288,463,695,1105]
assert all(a[n+1]>a[n] for n in range(1,N))
for n in range(1,N+1):
    m=0
    while (m+1)*(m+2)//2<=n: m+=1
    assert a[n]>=factorial(m)
# Exact Gaussian-moment Edgeworth coefficients; coordinates are cumulant orders 3..10.
def dfodd(s):
    v=1
    for j in range(1,s,2): v*=j
    return v
terms={}
for R in range(5):
    orders=list(range(3,2*R+3)); found={}
    def rec(i,budget,exps):
        if i==len(orders):
            degree=sum(r*j for r,j in zip(orders,exps))
            if degree%2: return
            coeff=F((-1)**(degree//2)*dfodd(degree))
            for r,j in zip(orders,exps): coeff/=factorial(j)*factorial(r)**j
            found[tuple(exps)]=coeff
            return
        r=orders[i]
        for j in range(budget//(r-2)+1): rec(i+1,budget-(r-2)*j,exps+[j])
    rec(0,2*R,[])
    terms[str(R)]={','.join(map(str,e)):str(v) for e,v in sorted(found.items())}
assert terms['1']=={'0,0':'1','0,1':'1/8','2,0':'-5/24'}
# The usual second-order correction, independently evaluated Gaussian moments.
assert terms['2']['0,0,0,1']==str(F(-1,48))
assert terms['2']['1,0,1,0']==str(F(7,48))
assert terms['2']['0,2,0,0']==str(F(35,384))
assert terms['2']['2,1,0,0']==str(F(-35,64))
assert terms['2']['4,0,0,0']==str(F(385,1152))
# Rational checks of inverse h(x)=t*x-log(x) derivative formulas at x=m.
for m in (2,3,7,19):
  for L in (2,3,5,11):
    hp=F(L-1,m); hpp=F(1,m*m); hppp=F(-2,m**3)
    assert 1/hp==F(m,L-1)
    assert -hpp/hp**3==F(-m,(L-1)**3)
    assert (3*hpp**2-hppp*hp)/hp**5==F(m*(2*L+1),(L-1)**5)
receipt={'status':'PASS','scope':'Finite exact corroboration only; ordinary analytic proof is audited separately.','coefficient_identities':N+1,'strict_monotonicity_checks':N-1,'factorial_lower_bound_checks':N,'edgeworth_orders_checked':list(range(5)),'edgeworth_terms':terms,'inverse_derivative_identities':48,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='edgeworth_terms'},indent=2))
