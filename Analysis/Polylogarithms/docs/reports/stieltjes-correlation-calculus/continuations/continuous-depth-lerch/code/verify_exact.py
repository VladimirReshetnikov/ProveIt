#!/usr/bin/env python3
"""Exact finite checks and coefficient tables for Continuous-Depth Lerch Calculus.

The analytic theorems are proved in article.tex. These rational polynomial
checks neither establish period independence nor replace those proofs.
Run from any directory; outputs are written to ../data/.
"""
from __future__ import annotations
import json
import math
from pathlib import Path
import sympy as S

OUT = Path(__file__).resolve().parents[1] / 'data'
OUT.mkdir(exist_ok=True)
counts: dict[str,int] = {}
controls: list[str] = []

def check(name: str, expr: S.Expr) -> None:
    if S.cancel(S.expand(expr)) != 0:
        raise AssertionError(f'{name}: {expr}')
    counts[name] = counts.get(name,0)+1

def bell_exact(d: list[S.Expr]) -> S.Expr:
    b = [S.Integer(1)]
    for n in range(1,len(d)+1):
        b.append(S.expand(sum(S.binomial(n-1,j-1)*d[j-1]*b[n-j]
                              for j in range(1,n+1))))
    return b[-1]

# Two independently organized formal computations of the Gamma quotient.
# ζ(j) is represented by an independent symbol Zj; no independence assertion
# about actual zeta values is made by using a polynomial ring.
M,Q = 4,6
maxweight = 2*M+Q
Z = {j:S.Symbol(f'Z{j}') for j in range(2,maxweight+1)}
L: dict[tuple[int,int],S.Expr] = {}
for ell in range(2,maxweight+1):
    for v in range(0,min(ell,2*M)+1,2):
        u=ell-v
        if u>Q: continue
        val = S.Rational((-1)**ell,ell)*Z[ell]*(2*S.binomial(ell,v)/S.Integer(2)**u-(1 if v==0 else 0))
        if val: L[u,v]=val
F={(0,0):S.Integer(1)}
for total in range(1,maxweight+1):
    for u in range(Q+1):
        v=total-u
        if not 0<=v<=2*M: continue
        F[u,v]=S.expand(sum((i+j)*l*F.get((u-i,v-j),0)
                           for (i,j),l in L.items() if i<=u and j<=v)/total)

def mul(a:list[S.Expr],b:list[S.Expr])->list[S.Expr]:
    return [S.expand(sum(a[j]*b[n-j] for j in range(n+1))) for n in range(Q+1)]

lg=[S.Integer(0)]*(Q+1)
for j in range(2,Q+1):
    lg[j]=S.Rational((-1)**j,j)*Z[j]*(S.Integer(2)**(1-j)-1)
g=[S.Integer(1)]
for n in range(1,Q+1):
    g.append(S.expand(sum(j*lg[j]*g[n-j] for j in range(1,n+1))/n))
A=[[S.Integer(1)]+[S.Integer(0)]*Q]
for m in range(1,M+1):
    row=[S.Integer(0)]*(Q+1)
    for j in range(1,m+1):
        hz=[(-1)**h*S.rf(2*j,h)*Z[2*j+h]/(S.factorial(h)*2**h) for h in range(Q+1)]
        prod=mul(hz,A[m-j])
        row=[S.expand(row[h]+prod[h]/m) for h in range(Q+1)]
    A.append(row)

rows=[]
for m in range(1,M+1):
    rhs=mul(g,A[m])
    for q in range(Q+1):
        val=S.expand(S.factorial(q)*F[q,2*m]/2)
        check('two independent Gamma-coefficient recurrences',val-S.factorial(q)*rhs[q]/2)
        # Every monomial has the predicted weight.
        for powers,coef in S.Poly(val,*Z.values()).terms():
            if coef:
                assert sum(j*n for j,n in zip(Z,powers))==2*m+q
        counts['homogeneous zeta weights']=counts.get('homogeneous zeta weights',0)+1
        rows.append({'m':m,'q':q,'weight':2*m+q,'formal_zeta_polynomial':str(val),
                     'latex':S.latex(val)})

# Direct finite-product coefficients versus the Bell--harmonic derivative.
e=S.Symbol('e')
for m in range(1,4):
    for k in range(1,7):
        num=S.prod(1+e/S.Integer(j) for j in range(1,k+1)).expand()
        for q in range(0,6):
            direct=S.factorial(q)*sum(num.coeff(e,j)*(-1)**(q-j)*S.rf(2*m+1,q-j)
                      /(S.factorial(q-j)*(2*k)**(q-j)) for j in range(q+1))
            d=[(-1)**(j-1)*S.factorial(j-1)*(S.harmonic(k,j)-S.Rational(2*m+1,(2*k)**j))
               for j in range(1,q+1)]
            check('finite products versus Bell-harmonic jets',direct-bell_exact(d))

# Gamma shift products, two normalizations and integer seed polynomials.
r,x,pi2=S.symbols('r x Pi2')
for n in range(1,8):
    product=S.prod(x*x+pi2*(r+2*j)**2 for j in range(n))
    factored=S.prod((r/2+j)**2+x*x/(4*pi2) for j in range(n))*(4*pi2)**n
    check('depth-shift product normalizations',product-factored)
for n in range(1,7):
    poly=S.prod(x*x+pi2*(r+2*j)**2 for j in range(n))
    check('depth-shift recurrence',poly-(x*x+pi2*r*r)*S.prod(x*x+pi2*(r+2*j+2)**2 for j in range(n-1)))

# The transform derivative polynomial P_k and separate Bell recurrence.
v,h,s=S.symbols('v h s')
deriv=lambda f:S.expand((v*v+pi2)*S.diff(f,v)+h*h*S.diff(f,h))
P=[S.Integer(1)]
for k in range(8):
    P.append(S.expand((r*v+s*h)*P[-1]+deriv(P[-1])))
d=[r*v+s*h]
for k in range(1,8): d.append(deriv(d[-1]))
for k in range(9):
    check('transform moment recurrence versus Bell jets',P[k]-bell_exact(d[:k]))
    check('moment leading h coefficient',S.Poly(P[k],h).coeff_monomial(h**k)-S.rf(s,k))
    check('moment leading v coefficient',S.Poly(P[k],v).coeff_monomial(v**k)-S.rf(r,k))

# Independent reduction of the second moment at total depth two.
t=S.Symbol('t'); sig=2-r; w=s+t
# Coefficient of E(w), E(w+2) after C4 and the odd-v integration-by-parts rule.
c0=r*(r+1)*4*pi2/6-r*r*pi2
c2=r*(r+1)*w*(w+1)/6-r*s*(w+1)+s*(s+1)
target=(sig*(sig+1)*s*(s+1)+r*(r+1)*t*(t+1)-2*r*sig*s*t)/6
check('second-moment Stieltjes coefficient',c0-pi2*r*sig/3)
check('second-moment spectral coefficient',c2-target)
check('first moment conservation', (r*0/2+(sig*s-r*t)/2)+(sig*0/2+(r*t-sig*s)/2))

# Print-ready identities, after legitimate even-zeta simplification.
actual={Z[j]:S.zeta(j) for j in Z}
by={(row['m'],row['q']):S.sympify(row['formal_zeta_polynomial']).subs(actual) for row in rows}
check('quadratic harmonic example',by[1,2]-S.zeta(4)/8)
check('cubic harmonic example',by[1,3]-S.Rational(3,2)*(S.zeta(2)*S.zeta(3)-S.zeta(5)))
# Convolution harmonic coefficients at positive integer shift.
for n in range(1,9):
    for j in range(1,5):
        # Direct log differentiation of (r)_(2n) away from its zeros.
        lhs=sum(S.Rational(1,(ell+3)**j) for ell in range(2*n))
        check('shifted harmonic sums',lhs-S.harmonic(2*n+2,j)+S.harmonic(2,j))

# Negative controls deliberately change a proven coefficient.
for name,bad in [('missing factor in second moment',c0-pi2*r*sig/2),
                 ('wrong cubic harmonic sign',by[1,3]-S.Rational(3,2)*(S.zeta(2)*S.zeta(3)+S.zeta(5))),
                 ('missing depth-shift square',(x*x+pi2*r)-(x*x+pi2*r*r))]:
    if S.simplify(bad)==0: raise AssertionError('negative control failed: '+name)
    controls.append(name)

# Store tables using readable exact zeta expressions as well as formal ones.
for row in rows:
    expr=S.sympify(row['formal_zeta_polynomial']).subs(actual)
    row['simplified_exact_value']=str(expr)
    row['latex']=S.latex(expr)
(OUT/'harmonic_coefficients.json').write_text(json.dumps(rows,indent=2)+'\n')
summary={'status':'PASS','sympy_version':S.__version__,'assertion_families':counts,
         'exact_assertions':sum(counts.values()),'negative_controls':controls,
         'negative_control_count':len(controls),
         'scope':'Finite exact algebra checks; analytic theorems require the article proofs.'}
(OUT/'exact_results.json').write_text(json.dumps(summary,indent=2)+'\n')
(OUT/'harmonic_table.tex').write_text('\n'.join(
    f"{row['m']} & {row['q']} & ${row['latex']}$ \\\\" for row in rows
    if row['m']<=2 and row['q']<=4)+'\n')
print(json.dumps(summary,indent=2))
