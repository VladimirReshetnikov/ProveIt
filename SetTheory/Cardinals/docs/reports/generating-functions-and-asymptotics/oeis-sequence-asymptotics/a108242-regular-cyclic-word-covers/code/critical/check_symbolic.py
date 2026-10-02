"""Exact formal arithmetic through h^3; computations are not uniform-error proofs.

The finite slot enumeration includes all singletons and each one-pair merger.
Only U2 copies b, V1 copies d<=3, and one U3 can affect these coefficients.
No candidate coefficients are used to construct the result.
"""
import json
from pathlib import Path
import sympy as S
h, lam, b, theta = S.symbols('h lambda b theta')
K=3

def trunc(p):
    p=S.expand(p)
    return sum(p.coeff(h,k)*h**k for k in range(K+1))

def f(t):
    return S.prod(1-i*h/lam for i in range(t))

def p2power(q):
    return sum(S.prod(q-i for i in range(k))/S.factorial(k)*(-h/lam)**k for k in range(K+1))

def moment(poly):
    # E[b^m] for a formal Poisson variable of mean theta, without numerical fitting.
    out=0
    for (m,), c in S.Poly(S.expand(poly),b).terms():
        T=sum(S.functions.combinatorial.numbers.stirling(m,j,kind=2)*theta**j for j in range(m+1))
        out+=c*T
    return S.factor(out)

raw=0
for d in range(4):
    M=3*b+d; J=2*b+d
    singleton=trunc(p2power(3*b)*f(3)**d*(1-M*(M-1)*h**2/2)*(1+3*J**2*h**3/lam))
    pairs=0
    # Each term is the polynomial weight of the corresponding merged block.
    pairs += (3*b)*(3*b-1)/2 * trunc(f(4)*p2power(3*b-2)*f(3)**d)
    if d:
        pairs += 3*b*d*trunc(f(5)*p2power(3*b-1)*f(3)**(d-1))
    if d>=2:
        pairs += S.Integer(d*(d-1))/2*trunc(f(6)*p2power(3*b)*f(3)**(d-2))
    raw += trunc((2*lam*h/3)**d/S.factorial(d) * (singleton+h**2*pairs))
# The sole U3 mode has weight h^3; to this order all its other factors are one.
raw=trunc(raw+lam**3*h**3/9)
coeff=[S.factor(raw.coeff(h,k)) for k in range(4)]
poisson=[moment(x) for x in coeff]
expected={
    1:[S.Integer(1),lam/6,lam**2/72-S.Rational(3,2),S.Rational(7,6)/lam-lam/4-S.Rational(71,1296)*lam**3],
    -1:[S.Integer(1),7*lam/6,49*lam**2/72-S.Rational(5,2),S.Rational(3,2)/lam-35*lam/12+S.Rational(271,1296)*lam**3]
}
report={'raw_coefficients_after_dividing_theta_power_by_b_factorial':[str(x) for x in coeff], 'poisson_coefficients_before_theta_substitution':[str(x) for x in poisson], 'models':{}}
for s in [1,-1]:
    P=[S.factor(x.subs(theta,s*lam**2/6)) for x in poisson]
    assert all(S.simplify(x-y)==0 for x,y in zip(P,expected[s]))
    L=[P[1],S.factor(P[2]-P[1]**2/2),S.factor(P[3]-P[1]*P[2]+P[1]**3/3)]
    report['models'][str(s)]={'P':[str(x) for x in P], 'log_corrections':[str(x) for x in L], 'candidate_match':True}
p=Path(__file__).with_name('symbolic-results.json');p.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
