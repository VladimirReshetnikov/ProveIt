#!/usr/bin/env python3
"""Exact symbolic regression checks, not a formal proof assistant.

All checks use rational arithmetic and symbolic indeterminates.  No numerical
identity search is used.  The analytic proofs are in the accompanying article.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    checks: list[str] = []
    def equal(label: str, lhs, rhs) -> None:
        residue = s.cancel(s.expand(lhs-rhs))
        if residue != 0:
            raise AssertionError((label, residue))
        checks.append(label)

    y,z,u,t = s.symbols('y z u t')
    Z = {j:s.Symbol(f'Z{j}') for j in range(2,11)}
    N=8
    # Coefficients of the exponential generating function, independently from
    # the displayed polynomial recurrence.
    gen=s.Integer(1)
    factors=[(1,y)] + [(j,(-1)**(j+1)*Z[j]/j) for j in range(2,N+1)]
    for j,c in factors:
        fac=sum((c*z**j)**r/s.factorial(r) for r in range(N//j+1))
        gen=s.Poly(s.expand(gen*fac),z)
        gen=sum(co*z**de[0] for de,co in gen.terms() if de[0]<=N)
    P=[s.Integer(1)]
    for n in range(N):
        P.append(s.expand(y*P[n]+sum((-1)**j*s.factorial(n)/s.factorial(n-j)*Z[j+1]*P[n-j] for j in range(1,n+1))))
        equal(f'Appell EGF degree {n+1}',P[-1],s.expand(gen).coeff(z,n+1)*s.factorial(n+1))
        equal(f'Appell derivative degree {n+1}',s.diff(P[-1],y),(n+1)*P[n])
    expected={2:y*y-Z[2],3:y**3-3*Z[2]*y+2*Z[3],
        4:y**4-6*Z[2]*y*y+8*Z[3]*y+3*Z[2]**2-6*Z[4],
        5:y**5-10*Z[2]*y**3+20*Z[3]*y*y+(15*Z[2]**2-30*Z[4])*y+24*Z[5]-20*Z[2]*Z[3]}
    for n,p in expected.items():equal(f'displayed polynomial P{n}',P[n],p)

    # The centered gamma moments from the cumulant recurrence.
    mu=[s.Integer(1),s.Integer(0)]
    for n in range(2,9):
        mu.append(s.expand(sum(s.binomial(n-1,j-1)*s.factorial(j-1)*u**(j-1)*mu[n-j] for j in range(2,n+1))))
    expected_mu={2:u,3:2*u*u,4:3*u*u+6*u**3,
                 5:20*u**3+24*u**4,6:15*u**3+130*u**4+120*u**5}
    for j,v in expected_mu.items():equal(f'gamma centered moment {j}',mu[j],v)
    f=s.symbols('f0:9')
    smooth=s.expand(sum(t**j*f[j]*mu[j]/s.factorial(j) for j in range(9)))
    for j,v in {1:t*t*f[2]/2,2:t**3*f[3]/3+t**4*f[4]/8,
                3:t**4*f[4]/4+t**5*f[5]/6+t**6*f[6]/48}.items():
        equal(f'smoothing coefficient {j}',smooth.coeff(u,j),v)

    # Algebraic inversion at a simple zero.
    f1,f2,f3,f4=s.symbols('f1 f2 f3 f4',nonzero=True)
    A=t*t*f2/2; Ap=t*f2+t*t*f3/2; B=t**3*f3/3+t**4*f4/8
    u1=-A/f1;u2=-(f2*u1*u1/2+Ap*u1+B)/f1
    C=u1*u1/t**3-u2/t**2
    displayed=t*t*(f2/f1)**3/8-t*(f2/f1)**2/4-t*t*f2*f3/(4*f1*f1)+t*f3/(3*f1)+t*t*f4/(8*f1)
    equal('general root inverse-order correction',C,displayed)
    equal('general root constant correction',-u1/t**2,f2/(2*f1))
    b=s.symbols('b')
    ratios={f1:1,f2:-2*b-1/t,
        f3:3*b+6*b*b+3*b/t+2/t**2,
        f4:-4*b-24*b*b-24*b**3-6*(b+2*b*b)/t-8*b/t**2-6/t**3}
    first=1/(24*t)+t*b*(1+b)-t*t*b*(1+b)*(1+2*b)/2
    equal('first-index correction',displayed.subs(ratios),first)

    # Cancellation of conductor and harmonic-number cumulants.
    g,lq,lp,H=s.symbols('g logq log2pi H')
    equal('first universal cumulant',(g+lp-lq-H)+lq+H,g+lp)
    for nu in (0,1):
        for m in range(2,11):
            Hm=s.Symbol(f'H{m}')
            cm=(s.factorial(m-1)*(Z[m]-Hm) if m%2 else
                s.factorial(m-1)*(Hm+(-1)**nu*(1-s.Rational(2)**(1-m))*Z[m]))
            factorial_cumulant=(-1)**(m-1)*s.factorial(m-1)*Hm
            target=(s.factorial(m-1)*Z[m] if m%2 else
                    (-1)**nu*s.factorial(m-1)*(1-s.Rational(2)**(1-m))*Z[m])
            equal(f'universal cumulant parity {nu} degree {m}',cm+factorial_cumulant,target)

    # Finite logarithmic derivative polynomials used by the exact verifier.
    from exact_verify import elementary
    ellmax=5
    def Q(n:int,ell:int):
        es=elementary(ell,n)
        return sum(s.factorial(n)*s.Rational(es[n-j].numerator,es[n-j].denominator)*(-y)**j/s.factorial(j) for j in range(n+1))
    for ell in range(1,ellmax+1):
        for n in range(6):
            equal(f'finite Q derivative n={n} ell={ell}',
                  s.diff(Q(n,ell),y)-(ell+1)*Q(n,ell),-(ell+1)*Q(n,ell+1))
    out={'status':'PASS','sympy_version':s.__version__,'arithmetic':'exact symbolic rational arithmetic',
         'checks_count':len(checks),'checks':checks}
    (ROOT/'data/symbolic_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(f'PASS: {len(checks)} exact symbolic regression checks.')

if __name__=='__main__':main()
