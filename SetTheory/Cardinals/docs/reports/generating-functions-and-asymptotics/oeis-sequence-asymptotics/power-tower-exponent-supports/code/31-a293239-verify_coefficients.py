"""Exact checks for the A293239 coefficient and tanh identities.

Finite regressions supplement the analytic proof; they do not establish an
infinite zero classification. Requires only Python's standard library.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import hashlib
import json

LIMIT=48

def mul(a,b):
    c=[F(0)]*min(LIMIT+1,len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:len(c)-i]):
                if y:c[i+j]+=x*y
    return c

log=[F(0)]+[F((-1)**(j+1),j) for j in range(1,LIMIT+1)]
at=[F(0)]+[F(1,j) if j%2 else F(0) for j in range(1,LIMIT+1)]
lp=[F(1)]; ap=[F(1)]; digest=hashlib.sha256(); count=zeros=0
for d in range(1,13):
    lp=mul(lp,log);ap=mul(ap,at)
    plus=[F(comb(d,j)) for j in range(d+1)]
    left=mul(lp,plus)
    for M in range(d,LIMIT+1):
        exponent=M-d-1
        minus=([F(1)]*(LIMIT+1) if exponent==-1 else
               [F(comb(exponent,j)*(-1)**j) for j in range(exponent+1)])
        right=mul(mul(ap,plus),minus)
        lhs=left[M]; rhs=right[M]/2**(M-d)
        if lhs!=rhs:raise RuntimeError(('coefficient mismatch',M,d,lhs,rhs))
        value=lhs*F(factorial(M),factorial(d))
        if value.denominator!=1:raise RuntimeError(('noninteger',M,d,value))
        count+=1;zeros+=value==0;digest.update(f'{M},{d}:{value}\n'.encode())

# Independently replay the coefficient recurrence and the derivative recurrence.
cap=200
rows=[[1]]; derivative={(0,0):1}; zero_count=0; snapshots=[]
for n in range(1,cap+1):
    row=[0]*(n+1)
    for d in range(1,n+1):
        r1=rows[n-1]
        a=r1[d-1]
        b=(d-n+1)*(r1[d] if d<len(r1) else 0)
        c=(n-1)*(rows[n-2][d-1] if n>=2 and d-1<len(rows[n-2]) else 0)
        row[d]=a+b+c
    rows.append(row);zero_count+=sum(v==0 for v in row[1:])
    new={}
    def add(key,v):new[key]=new.get(key,0)+v
    for (h,j),v in derivative.items():
        add((h,j),v);add((h,j+1),v)
        if j:add((h+1,j-1),j*v)
        if h:add((h+1,j),-h*v)
    derivative={key:v for key,v in new.items() if v}
    expected={}
    for M in range(n+1):
        for d,v in enumerate(rows[M]):
            if v:expected[(M-d,n-M)]=comb(n,M)*v
    if derivative!=expected:raise RuntimeError(('derivative mismatch',n))
    if len(derivative)!=1+n*(n+1)//2-zero_count:raise RuntimeError(('count mismatch',n))
    if n in (1,2,5,8,10,50,100,200):
        snapshots.append({'N':n,'term_count':len(derivative),'triangle_zeros':zero_count})
result={'coefficient_identities':count,'zero_cases_in_identity_check':zeros,
        'identity_digest':digest.hexdigest(),'derivative_orders_checked':cap,
        'snapshots':snapshots,'scope':'finite exact regression only'}
Path(__file__).with_name('coefficient_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
