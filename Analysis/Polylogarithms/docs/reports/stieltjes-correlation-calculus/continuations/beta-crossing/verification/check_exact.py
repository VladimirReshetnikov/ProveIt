#!/usr/bin/env python3
"""Exact finite checks accompanying the proofs; no numerical equality tests.
Run from any working directory. Writes exact_results.json beside this script.
"""
from __future__ import annotations
import json, random, platform
from pathlib import Path
import sympy as S
from collections import Counter

counts: Counter[str] = Counter()
u,t,a,n,X,L,V = S.symbols('u t a n X L V')

def check(name: str, expr: S.Expr) -> None:
    value = S.cancel(S.expand(expr))
    if value != 0:
        raise AssertionError(f'{name}: {value}')
    counts[name] += 1

# Independent finite Leibniz proof of the beta density derivative.
for m in range(1, 13):
    b = m-a
    lhs = sum(S.binomial(m-1,j)*S.ff(b-1,j)*(-1)**(m-1-j)
              *S.ff(a-1,m-1-j)*t**(m-1-j)*(1-t)**j
              for j in range(m))
    check('beta_density_derivative', lhs-S.prod(b-h for h in range(1,m)))

# Multiplicity polynomial and its differential recurrence.
for m in range(1, 13):
    C = S.Poly(S.prod(X+j-a for j in range(1,m)), X)
    check('multiplicity_polynomial', C.as_expr().subs(X,n+a)-S.prod(n+j for j in range(1,m)))
    check('multiplicity_derivative', S.diff(C.as_expr(),a)+S.diff(C.as_expr(),X))
    for j in range(1,m):
        check('coefficient_derivative', S.diff(C.nth(j-1),a)+j*C.nth(j))

# Jet coefficients: direct sine/exponential convolution versus two powers.
for q in range(14):
    direct = S.I*sum(S.binomial(q,k)*(-1)**((k-1)//2)*(S.pi*V)**k*L**(q-k)
                     for k in range(1,q+1,2))
    check('contact_jet_polynomial', direct-((L+S.I*S.pi*V)**q-(L-S.I*S.pi*V)**q)/2)
    direct_cos = sum(S.binomial(q,k)*(-1)**(k//2)*(S.pi*V)**k*L**(q-k)
                     for k in range(0,q+1,2))
    check('finite_part_jet_polynomial', direct_cos-((L+S.I*S.pi*V)**q+(L-S.I*S.pi*V)**q)/2)

# Rank of the contact map on sum(v)=0; exact rational twists, fixed seed.
rng = random.Random(20261010)
for d in range(2,10):
    for case in range(15):
        theta = [S.Rational(rng.randrange(-18,25),5)+S.Rational(1,101) for _ in range(d)]
        occupied = len({S.floor(x) for x in theta})
        lo,hi = int(S.floor(min(theta))),int(S.ceiling(max(theta)))
        rows=[]
        for k in range(lo,hi+1):
            inds=[int(bool(x<k)) for x in theta]
            if 0<sum(inds)<d:
                rows.append([inds[j]-inds[-1] for j in range(d-1)])
        rank=S.Matrix(rows).rank() if rows else 0
        if rank != occupied-1:
            raise AssertionError((theta,rank,occupied))
        counts['chamber_rank']+=1

# Two independently derived all-moment formulas agree as formal combinations
# of independent zeta symbols. This tests rational cancellation and parity.
def hz_integer(k:int,r:int):
    return S.Symbol(f'Z{k}')-sum(S.Rational(1,j**k) for j in range(1,r))
for r in range(1,7):
    for s in range(1,7):
        m=r+s
        P=S.Poly(S.prod(j+u for j in range(1,r))*S.prod(j-u for j in range(1,s)),u)
        cr=S.Poly(S.prod(X+j-r for j in range(1,m)),X)
        cs=S.Poly(S.prod(X+j-s for j in range(1,m)),X)
        for q in range(m,m+6):
            mellin=S.factorial(q)/S.factorial(m-1)*( 
                (-1)**q*sum(cr.nth(k)*hz_integer(q+1-k,r) for k in range(m))
                +(-1)**m*sum(cs.nth(k)*hz_integer(q+1-k,s) for k in range(m)))
            cot=(-1)**(r+1)*2*S.factorial(q)/S.factorial(m-1)*sum(
                P.nth(q-2*k)*S.Symbol(f'Z{2*k}') for k in range(1,q//2+1))
            check('moment_mellin_vs_cotangent',mellin-cot)

# Gamma-prefactor mixing at a simple pole. Formal coefficients, arbitrary q.
e=S.symbols('e')
for q in range(11):
    gs=S.symbols(f'g0:{q+2}')
    cs=S.symbols(f'c0:{q+1}')
    rho=S.symbols('rho')
    G=sum(gs[j]*e**j for j in range(q+2))
    H=rho/e+sum(cs[j]*e**j for j in range(q+1))
    actual=S.expand(G*H).coeff(e,q)
    expected=rho*gs[q+1]+sum(gs[j]*cs[q-j] for j in range(q+1))
    check('gamma_pole_mixing',actual-expected)

# Formal derivative of the polylog primitive, using d Li_j /du = c Li_(j-1).
c=S.symbols('c',nonzero=True)
for r in range(1,6):
    for s in range(1,6):
        R=S.Poly(u*S.prod(j+u for j in range(1,r))*S.prod(j-u for j in range(1,s)),u).as_expr()
        d=S.degree(R,u)
        deriv=0
        for j in range(d+1):
            deriv+=(-1)**j*(S.diff(R,u,j+1)*S.Symbol(f'Li{j+1}')/c**j
                  +S.diff(R,u,j)*S.Symbol(f'Li{j}')/c**(j-1))
        check('polylog_primitive_telescoping',deriv-c*R*S.Symbol('Li0'))

# Explicit normalization controls.
check('explicit_constants',S.I/(2*S.pi*S.I)*2-1/S.pi)
check('explicit_constants',(-1)*4/(2*(2*S.pi*S.I)**2)*((S.I*S.pi)-(-S.I*S.pi))-S.I/S.pi)
check('explicit_constants',(-1)*4/(2*(2*S.pi*S.I)**2)*((S.I*S.pi)**3-(-S.I*S.pi)**3)+S.I*S.pi)
# Deliberately uncorrected candidate formulas must retain a nonzero residual.
# Each is tied to an explicit example in the article, rather than perturbing
# an unrelated expression. These are symbolic rejection tests, not intervals.
negative_controls = {
    'omit_half_twist_crossing': S.Rational(1,1)/S.pi-S.cos(S.pi/2)/S.pi,
    'differentiate_integer_only_formula':
        S.diff(S.exp(S.I*S.pi*u)/S.pi**2-S.cos(S.pi*u)/S.pi**2,u).subs(u,0),
    'omit_gamma_residue_term': S.EulerGamma-S.Integer(1),
}
for name, bad in negative_controls.items():
    if S.simplify(bad)==0:
        raise AssertionError(f'corruption control failed: {name}')
    counts['rejected_corruptions']+=1

result={'status':'PASS','python':platform.python_version(),'sympy':S.__version__,
        'checks_by_family':dict(counts),'total_exact_checks':sum(counts.values()),
        'rejected_candidate_residuals':{name:str(S.simplify(expr)) for name,expr in negative_controls.items()},
        'scope':'Finite checks support the human proofs; no proof-assistant formalization.'}
out=Path(__file__).with_name('exact_results.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
