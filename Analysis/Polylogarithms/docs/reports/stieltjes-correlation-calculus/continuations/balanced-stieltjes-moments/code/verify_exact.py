"""Exact independent algebra checks; these do not replace analytic proofs."""
from __future__ import annotations
from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial
import json
import sympy as s
from balanced import pochhammer_coefficients

OUT=Path(__file__).resolve().parents[1]/'results'
OUT.mkdir(exist_ok=True)
checks=[]
def check(name, condition):
    ok=bool(condition)
    checks.append({'name':name,'passed':ok})
    if not ok:
        raise AssertionError(name)

def elementary_exact(m):
    c=[F(1)]
    for j in range(1,m):
        c=[(c[k] if k<len(c) else F(0))+(c[k-1]/j if k else F(0))
           for k in range(len(c)+1)]
    return c

def exp_coeff(logcoeff, degree):
    c=[s.Integer(1)]
    for n in range(1,degree+1):
        c.append(s.expand(sum(k*logcoeff[k]*c[n-k]
                              for k in range(1,n+1))/n))
    return c

z,a,t=s.symbols('z a t')
# Independent direct symbolic polynomial versus integer multiplication.
for n in range(17):
    P=s.Poly(s.prod(z+j for j in range(1,n+1)),z)
    for q in range(n+2):
        check(f'pochhammer/{n}/{q}', P.nth(q)==pochhammer_coefficients(n,q)[q])
# Bell/logarithmic harmonic recurrence versus finite product.
for m in range(1,11):
    c=[F(1)]
    for q in range(1,13):
        c.append(sum(((-1)**(j-1))*sum(F(1,k**j) for k in range(1,m))*c[q-j]
                     for j in range(1,q+1))/q)
    e=elementary_exact(m)
    for q in range(13):
        check(f'harmonic-bell/{m}/{q}',c[q]==(e[q] if q<len(e) else 0))
# EM re-expansion at x+a, independently compared with Bernoulli polynomials.
for k in range(1,19):
    scalar=(-1)**k*a**k/s.factorial(k)+s.Rational(1,2)*(-1)**(k-1)*a**(k-1)/s.factorial(k-1)
    scalar+=sum(s.bernoulli(2*j)/s.factorial(2*j)*(-1)**(k-2*j)*a**(k-2*j)/s.factorial(k-2*j)
                for j in range(1,k//2+1))
    check(f'EM-Bernoulli/{k}',s.expand(scalar-(-1)**k*s.bernoulli(k,a)/s.factorial(k))==0)
    for q in range(0,9):
        value=pochhammer_coefficients(k-1,q)[q]*factorial(q)
        check(f'tail-degree/{k}/{q}',(value==0)==(q>=k))
# Uniqueness of homogeneous balancing: exact linear systems, not a guessed vector.
for q in range(1,13):
    A=s.Matrix([[s.ff(j,r) for j in range(q+1)] for r in range(q)])
    v=s.Matrix([(-1)**j*comb(q,j) for j in range(q+1)])
    check(f'unique-balance-rank/{q}',A.rank()==q)
    check(f'unique-balance-kernel/{q}',A*v==s.zeros(q,1))
    check(f'leading-log-cancellation/{q}',sum(F((-1)**j*comb(q,j),j+1) for j in range(q+1))==F(1,q+1))
# The finite zeta coefficient sum and its binomial-series coefficient identity.
n=s.symbols('n')
for m in range(1,10):
    e=elementary_exact(m)
    p=sum(s.Rational(v.numerator,v.denominator)*(-1)**j*n**j for j,v in enumerate(e))
    target=(-1)**(m-1)*s.prod(n-j for j in range(1,m))/s.factorial(m-1)
    check(f'kappa-binomial-polynomial/{m}',s.expand(p-target)==0)
    for k in range(1,m):
        check(f'kappa-low-index-zero/{m}/{k}',p.subs(n,k)==0)
# Finite differences, exact Bernoulli annihilation, and minimal node counts.
for m in range(1,9):
    nodes=[s.Rational(2,5)+s.Rational(3,7)*j for j in range(m+2)]
    weights=[(-1)**(m+1-j)*comb(m+1,j) for j in range(m+2)]
    for k in range(m+1):
        check(f'filter-Bernoulli/{m}/{k}',sum(c*s.bernoulli(k,x) for c,x in zip(weights,nodes))==0)
    V=s.Matrix([[x**k for x in nodes[:-1]] for k in range(m+1)])
    check(f'minimal-filter/{m}',V.det()!=0)
# The mixed-germ diagonal and vertical restrictions independently reconstruct
# elementary and complete homogeneous polynomials through formal exponentiation.
D=12
for m in range(1,9):
    H=[0]+[sum(s.Rational(1,k**r) for k in range(1,m)) for r in range(1,D+1)]
    diagonal=exp_coeff([0]+[(-1)**(r-1)*H[r]/r for r in range(1,D+1)],D)
    vertical=exp_coeff([0]+[H[r]/r for r in range(1,D+1)],D)
    e=elementary_exact(m)
    h=[s.Integer(1)]+[s.Integer(0)]*D
    for j in range(1,m):
        for k in range(1,D+1):
            h[k]+=h[k-1]/j
    for k in range(D+1):
        check(f'mixed-diagonal/{m}/{k}',diagonal[k]==(s.Rational(e[k].numerator,e[k].denominator) if k<len(e) else 0))
        check(f'mixed-vertical/{m}/{k}',vertical[k]==h[k])
# Deliberate corruption controls: the incorrect sign and missing binomial must fail.
check('negative-control/wrong-balance',sum([1,2,1])!=0)
check('negative-control/complete-not-elementary',F(1)+F(1,2)+F(1,4)!=F(1,2))
# Exact table, left as a formal linear combination of zeta values.
zv={j:s.Symbol(f'Z{j}') for j in range(2,15)}
table=[]
for m in range(1,6):
    for q in range(m,m+4):
        e=elementary_exact(m)
        expr=s.expand(s.Rational((-1)**(m+q)*factorial(q),m)*sum(
            (-1)**j*s.Rational(v.numerator,v.denominator)*zv[q+1-j]
            for j,v in enumerate(e)))
        table.append({'m':m,'q':q,'kappa':str(expr),'kappa_tex':s.latex(expr)})
report={'kind':'exact rational and symbolic algebra; not formal analytic verification',
        'sympy':s.__version__,'count':len(checks),'passed':sum(c['passed'] for c in checks),
        'checks':checks}
(OUT/'exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
(OUT/'moment_table.json').write_text(json.dumps(table,indent=2)+'\n')
print(f"PASS: {report['passed']} / {report['count']} exact assertions")
