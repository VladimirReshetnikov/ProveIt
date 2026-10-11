#!/usr/bin/env python3
"""Exact finite-algebra regression tests; not a proof-assistant formalization."""
from __future__ import annotations
import itertools, json, math
from fractions import Fraction as Q
from pathlib import Path
import sympy as S

checks=[]
def check(name, lhs, rhs):
    residual=S.expand(lhs-rhs)
    if residual != 0:
        raise AssertionError(f'{name}: {residual}')
    checks.append({'name':name,'status':'passed'})

def parity(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def delta(xs):
    return S.prod(xs[j]-xs[i] for i in range(len(xs)) for j in range(i+1,len(xs)))

def main():
    s,z=S.symbols('s z')
    # Exact harmonic/Pochhammer coefficient identity.
    for l in range(1,19):
        poly=S.Poly(S.rf(s,l)/S.factorial(l),s)
        es=[S.Integer(1)]
        for j in range(1,l):
            es.append(S.Integer(0))
            for t in range(len(es)-1,0,-1): es[t]+=es[t-1]/j
        for t in range(1,l+1):
            check(f'pochhammer_l{l}_t{t}',poly.nth(t),es[t-1]/l)
    # Coefficient recurrence vs independent product of binomial polynomials.
    u,v=S.symbols('u v')
    aa=[S.Rational(1,3),S.Rational(-1,5)]
    C=[S.Integer(1)]
    for l in range(1,9):
        C.append(S.expand(sum((-1)**j*(u*aa[0]**j+v*aa[1]**j)*C[l-j] for j in range(1,l+1))/l))
        direct=sum((-aa[0])**j*S.rf(u,j)/S.factorial(j)*(-aa[1])**(l-j)*S.rf(v,l-j)/S.factorial(l-j) for j in range(l+1))
        check(f'binomial_recurrence_l{l}',C[l],direct)
    # Alternant orientation and normalization, including the 24-term case.
    for m in range(2,5):
        N=m*(m-1)//2
        w=list(range(m-1,-1,-1)); a=list(range(1,m+1))
        alt=sum(parity(p)*sum(w[p[j]]*a[j] for j in range(m))**N for p in itertools.permutations(range(m)))
        K=math.prod(math.factorial(k) for k in range(m))
        check(f'alternant_m{m}',alt,S.factorial(N)*delta(w)*delta(a)/K)
    # Full local jet with two poles of orders 3 and 2, polynomial P=x^3+2x.
    # Degree-r holomorphic polynomial is arbitrary and must be killed.
    A=S.symbols('A')
    L=A*sum((-1)**(j+1)*S.Rational(1,j)*z**j for j in range(1,7))+(1-A)*sum((-1)**(j+1)*S.Rational(3,j)*3**(j-1)*z**j for j in range(1,7))
    P={3:S.Integer(1),1:S.Integer(2)}
    residues={(1,3):S.Integer(2),(1,2):S.Integer(-3),(1,1):S.Integer(5),(2,2):S.Integer(7)}
    r=1
    F=11+13*A
    for (p,h),res in residues.items():
        degree=r+h
        coeff=sum(pk*S.expand(L**degree).coeff(z,k+p) for k,pk in P.items())
        F+=S.factorial(r)*res*(-1)**degree*coeff/S.factorial(degree)
    F=S.expand(F)
    d4=sum((-1)**(4-j)*S.binomial(4,j)*F.subs(A,A+j) for j in range(5))
    V=sum((-1)**(j+1)*(1-3**j)*z**j/j for j in range(1,7))
    target=2*sum(pk*S.expand(V**4).coeff(z,k+1) for k,pk in P.items())
    check('multiple_poles_top_difference',d4,target)
    d5=sum((-1)**(5-j)*S.binomial(5,j)*F.subs(A,A+j) for j in range(6))
    check('multiple_poles_next_difference',d5,0)
    # Exact finite-difference generating formula in an intermediate degree.
    q=2
    finite=sum((-1)**(q-j)*S.binomial(q,j)*F.subs(A,A+j) for j in range(q+1))
    direct=0
    for (p,h),res in residues.items():
        degree=r+h
        fd=sum((-1)**(q-j)*S.binomial(q,j)*(-1)**degree*(L+j*V)**degree/S.factorial(degree) for j in range(q+1))
        direct+=res*sum(pk*S.expand(fd).coeff(z,k+p) for k,pk in P.items())
    check('multiple_poles_intermediate_difference',finite,direct)
    # Laurent-product coefficients in independent Stieltjes coordinates.
    g=S.symbols('g0:4'); h=S.symbols('h0:4')
    G=1/s+sum((-1)**j*g[j]*s**j/S.factorial(j) for j in range(4))
    H=1/s+sum((-1)**j*h[j]*s**j/S.factorial(j) for j in range(4))
    prod=S.expand(G*H)
    for exponent,expected in [(-2,1),(-1,g[0]+h[0]),(0,g[0]*h[0]-g[1]-h[1]),(1,(g[2]+h[2])/2-g[0]*h[1]-g[1]*h[0])]:
        check(f'Stieltjes_product_coefficient_{exponent}',prod.coeff(s,exponent),expected)
    # Six-term local first jet, all lower coefficients retained symbolically.
    w=[2,1,0]; a=[S.Integer(1),S.Integer(2),S.Integer(3)]
    h0,c1,c2=S.symbols('h0 c1 c2')
    def local_first(weights):
        Lw=sum(weights[i]*sum((-1)**(j+1)*a[i]**j*z**j/j for j in range(1,4)) for i in range(3))
        # u=s*w: U=3s, first jet receives q=2 and q=3.
        return c1*S.expand(Lw**2).coeff(z,3)/6-c2*S.expand(Lw**3).coeff(z,3)/54+sum((i+1)*weights[i] for i in range(3))
    alt=sum(parity(p)*local_first([w[p[j]] for j in range(3)]) for p in itertools.permutations(range(3)))
    check('six_term_arbitrary_lower_residue',alt,S.Rational(2,9)*c2)
    # Bell compensation at first order, symbolic gamma and zeta(2).
    ell,z2,b0,b1=S.symbols('ell z2 b0 b1')
    K=1+ell*s+(ell**2+z2)*s**2/2
    check('untwisting_first_counterterm',S.expand(K*(1/s+b0-b1*s)).coeff(s,1),(ell**2+z2)/2+b0*ell-b1)
    out={'evidence':'exact rational/polynomial algebra; analytic proofs are in article.tex',
         'sympy_version':S.__version__,'checks_passed':len(checks),'checks':checks,
         'examples':{'divisor_six_term_shifts_1_2_3':'2/9','triple_divisor_constant_alternant':'2/27'}}
    path=Path(__file__).resolve().parents[1]/'results'/'exact_checks.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'checks_passed':len(checks),'output':str(path)}))

if __name__=='__main__': main()
