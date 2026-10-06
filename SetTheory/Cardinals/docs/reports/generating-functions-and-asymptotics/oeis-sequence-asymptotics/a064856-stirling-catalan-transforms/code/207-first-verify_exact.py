#!/usr/bin/env python3
"""Exact finite checks. Every guard remains active under python -O.

These checks verify identities and enumerated data, not analytic remainders.
Only the Python standard library is required.
"""
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path

checks = 0
def require(ok, message):
    global checks
    checks += 1
    if not ok:
        raise RuntimeError(message)

def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,v in enumerate(a): c[i]+=v
    for i,v in enumerate(b): c[i]+=v
    return trim(c)
def trim(a):
    while len(a)>1 and not a[-1]: a.pop()
    return a
def scale(a,b): return trim([b*v for v in a])
def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return trim(c)
def val(p,x):
    ans=F(0)
    for v in reversed(p): ans=ans*x+v
    return ans
def catalan(k): return math.comb(2*k,k)//(k+1)

oeis=[1,1,3,13,72,481,3745,33209,329868,3624270,43608474,
570008803,8039735704,121673027607,1966231022067,33786076421499,
615043147866660,11822938288619344,239298079351004608,
5086498410027323134,113278368771499790136,2637549737582063583274,
64082443707327038140602,1621782672366231029685407]
rows=[[1]]
for n in range(1,81):
    old=rows[-1]; new=[0]*(n+1)
    for k,v in enumerate(old):
        new[k]+=(n-1)*v
        new[k+1]+=v
    rows.append(new)
values=[sum(v*catalan(k) for k,v in enumerate(row)) for row in rows]
for n,v in enumerate(oeis): require(values[n]==v,f'OEIS term {n}')
for n in range(1,80): require(values[n+1]>n*values[n],f'increase {n}')

# Independent brute permutation cycle enumeration.
for n in range(9):
    row=[0]*(n+1)
    for p in itertools.permutations(range(n)):
        seen=set(); k=0
        for i in range(n):
            if i not in seen:
                k+=1; j=i
                while j not in seen:
                    seen.add(j);j=p[j]
        row[k]+=1
    require(row==rows[n],f'brute cycle row {n}')
    require(sum(row[k]*catalan(k) for k in range(n+1))==values[n],f'decorated sum {n}')

# Beta(1/2,3/2), scaled by 4, has Catalan moments.
moment=F(1)
for k in range(81):
    require(moment==catalan(k),f'beta moment {k}')
    moment*=4*F(2*k+1,2)/F(k+2)

# Independent polynomial product versus Stirling recurrence; marker included.
for n in range(31):
    p=[F(1)]
    for j in range(n): p=mul(p,[F(j),F(1)])
    require(p==[F(v) for v in rows[n]],f'rising polynomial {n}')
    for u in [F(1,2),F(1),F(3,2),F(2)]:
        polynomial_integral=sum(v*u**k*catalan(k) for k,v in enumerate(p))
        marked=sum(v*u**k*catalan(k) for k,v in enumerate(rows[n]))
        require(polynomial_integral==marked,f'marked integral {n},{u}')

# Bernoulli polynomials and compact gamma-ratio coefficient recurrence.
J=8
B=[F(1)]
for m in range(1,J+2):
    B.append(-sum(F(math.comb(m+1,k))*B[k] for k in range(m))/F(m+1))
bp={}
for m in range(1,J+1):
    poly=[F(math.comb(m+1,k))*B[m+1-k] for k in range(m+2)]
    poly[0]-=sum(poly)
    bp[m]=scale(poly,F((-1)**(m+1),m*(m+1)))
R=[[F(1)]]
for j in range(1,J+1):
    q=[F(0)]
    for m in range(1,j+1): q=add(q,scale(mul(bp[m],R[j-m]),F(m,j)))
    R.append(q)
require(R[1]==[F(0),F(-1,2),F(1,2)],'R1')
require(R[2]==[F(0),F(-1,12),F(3,8),F(-5,12),F(1,8)],'R2')
for s in range(0,19):
    exact=[F(1)]
    for i in range(1,s): exact=mul(exact,[F(1),F(i)])
    exact+= [F(0)]*(J+1-len(exact))
    for j in range(J+1): require(val(R[j],s)==exact[j],f'gamma positive shift {s},{j}')
for m in range(1,13):
    exact=[F(1)]+[F(0)]*J
    for r in range(1,m+1):
        exact=[sum(exact[k]*F(r)**(j-k) for k in range(j+1)) for j in range(J+1)]
    for j in range(J+1): require(val(R[j],-m)==exact[j],f'gamma negative shift {-m},{j}')

# Bernoulli cycle law, exact normalization and exact Ewens factorial moments.
for n in range(1,31):
    q=[F(1)]
    for j in range(n): q=mul(q,[F(j,j+4),F(4,j+4)])
    denom=math.prod(range(4,n+4))
    expected=[F(v*4**k,denom) for k,v in enumerate(rows[n])]
    require(q==expected,f'Ewens Bernoulli row {n}')
    mean=sum(k*p for k,p in enumerate(q))
    variance=sum((k-mean)**2*p for k,p in enumerate(q))
    require(mean==sum(F(4,j+4) for j in range(n)),f'Ewens mean {n}')
    require(variance==sum(F(4*j,(j+4)**2) for j in range(n)),f'Ewens variance {n}')
    norm=sum(q[k]*F(catalan(k),4**k) for k in range(n+1))
    require(norm==F(values[n],denom),f'Catalan tilt norm {n}')
    for k in range(n+1):
        require(q[k]*F(catalan(k),4**k)/norm==F(rows[n][k]*catalan(k),values[n]),f'RN {n},{k}')

result={'status':'PASS','checks':checks,'scope':'Finite exact identities only; no asymptotic or onset certification.',
        'oeis_terms':len(oeis),'brute_permutations_through_n':8,
        'gamma_ratio_polynomials':[[str(v) for v in p] for p in R],
        'terms_through_80':[str(v) for v in values]}
print(json.dumps(result,indent=2,sort_keys=True))
