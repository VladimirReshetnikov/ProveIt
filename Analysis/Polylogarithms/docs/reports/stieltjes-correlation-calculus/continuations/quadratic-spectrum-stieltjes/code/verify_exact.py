#!/usr/bin/env python3
"""Exact finite regression tests. These do not formalize the analytic proofs."""
from __future__ import annotations
import argparse,json,math,platform
from pathlib import Path
import sympy as s


def bells(v):
    B=[s.S.One]
    for n in range(1,len(v)+1):
        B.append(s.expand(sum(s.binomial(n-1,k-1)*v[k-1]*B[n-k]
                           for k in range(1,n+1))))
    return B


def run():
    counts={}
    def check(name,expr):
        assert s.simplify(expr)==0,(name,expr)
        counts[name]=counts.get(name,0)+1
    e,x,b,p=s.symbols('e x b p',nonzero=True)
    # Pochhammer differentiation with both harmonic coordinate systems.
    for alpha in [s.S.Half,s.S.One]:
        for k in range(1,11):
            poly=s.prod(alpha+e+j for j in range(k)).expand()
            v=[(-1)**(r-1)*s.factorial(r-1)*sum((j+alpha)**(-r) for j in range(k))
               for r in range(1,7)]
            B=bells(v)
            for m in range(7):
                check('pochhammer_bell',poly.coeff(e,m)*s.factorial(m)-s.rf(alpha,k)*B[m])
            for r in range(1,7):
                expected=s.harmonic(k,r) if alpha==1 else 2**r*s.harmonic(2*k,r)-s.harmonic(k,r)
                check('harmonic_conversion',sum((j+alpha)**(-r) for j in range(k))-expected)
    # Formal logarithm square; no assumptions about transcendental values.
    u=s.symbols('u')
    T=sum(2*s.I**(2*j+1)*u**(2*j+1)/s.Integer(2*j+1) for j in range(12))
    square=s.expand(T*T/4)
    anomaly=[]
    for k in range(1,13):
        expected=(-1)**k*(s.harmonic(2*k)-s.harmonic(k)/2)/k
        check('anomaly_harmonic',square.coeff(u,2*k)-expected)
        assert expected != 0
        counts['nonzero_parity_coefficient']=counts.get('nonzero_parity_coefficient',0)+1
        anomaly.append({'degree':2*k-1,'coefficient_of_b_power':str(expected),'power':2*k})
    for j in range(1,24,2):
        check('anomaly_even_weight_zero',square.coeff(u,j))
    # Rational partial fractions used by the finite polygamma formula.
    for N in range(1,7):
        rhs=0
        for r in range(1,N+1):
            A=(-1)**(N-r)*s.binomial(2*N-r-1,N-r)*(-2*s.I*b)**(-(2*N-r))
            Ac=(-1)**(N-r)*s.binomial(2*N-r-1,N-r)*(2*s.I*b)**(-(2*N-r))
            rhs+=A/(x+s.I*b)**r+Ac/(x-s.I*b)**r
        check('rational_partial_fractions',s.together(rhs-1/(x*x+b*b)**N))
    # Half-integer K polynomials: K_{nu+1}=K_{nu-1}+2nu K_nu/x.
    P=lambda m:sum(s.factorial(m+j)/(s.factorial(j)*s.factorial(m-j)*(2*x)**j)
                   for j in range(m+1))
    for m in range(1,13):
        check('half_integer_bessel_recurrence',P(m+1)-P(m-1)-(2*m+1)*P(m)/x)
    # Formal polylog derivative dictionary: d_b Li_r(exp(-2*pi*b+i*theta))=-2*pi Li_{r-1}.
    def L(m):
        local=-s.Integer(2)**(2*m+1)*s.factorial(m)**2*p*b**(2*m+1)/s.factorial(2*m+1)
        atoms={m+j+1:2*(-1)**m*s.factorial(m)*s.factorial(m+j)*b**(m-j)/
            (s.factorial(j)*s.factorial(m-j)*4**j*p**(m+j)) for j in range(m+1)}
        return local,atoms
    for m in range(1,11):
        local,atoms=L(m); prev_local,prev=L(m-1)
        check('mass_primitive_local',s.diff(local,b)-2*b*m*prev_local)
        deriv={}
        for r,c in atoms.items():
            deriv[r]=deriv.get(r,0)+s.diff(c,b)
            deriv[r-1]=deriv.get(r-1,0)-2*p*c
        for r in set(deriv)|set(prev):
            check('mass_primitive_polylogs',deriv.get(r,0)-2*b*m*prev.get(r,0))
    # Shift/mass PDE. d_a^2 Li_r = -4*pi^2 Li_{r-2}; terms cancel the b second derivatives.
    for m in range(11):
        local,atoms=L(m)
        check('shift_mass_PDE_local',s.diff(local,b,2)-2*m*s.diff(local,b)/b)
        residual={}
        for r,c in atoms.items():
            residual[r]=residual.get(r,0)+s.diff(c,b,2)-2*m*s.diff(c,b)/b
            residual[r-1]=residual.get(r-1,0)-4*p*s.diff(c,b)+4*m*p*c/b
        for expression in residual.values():
            check('shift_mass_PDE_polylogs',expression)
    # Residues and the inverse-square-root binomial coefficients.
    for j in range(13):
        check('heat_residue_normalization',s.sqrt(s.pi)*(-1)**j/
              (s.factorial(j)*s.gamma(s.S.Half-j))-s.binomial(2*j,j)/4**j)
    # Anchored Hurwitz primitive: exact Bernoulli-polynomial pole cancellation.
    a0=s.symbols('a0')
    for r in range(1,9):
        Br=s.bernoulli(r,x)
        remainder=Br-sum((x-a0)**j/s.factorial(j)*s.diff(Br,x,j).subs(x,a0)
                         for j in range(r))
        check('anchored_primitive_pole',remainder-(x-a0)**r)
    # Polynomial change of basis for the several-mass theorem.
    v=s.symbols('v')
    for D in range(9):
        poly=sum((-1)**j*(j+1)*v**j for j in range(D+1))
        changed=sum(s.diff(poly,v,j).subs(v,-b*b)/s.factorial(j)*(x*x+b*b)**j
                    for j in range(D+1))
        check('several_mass_polynomial_basis',poly.subs(v,x*x)-changed)
    return {'status':'PASS','kind':'exact finite algebra regressions, not analytic formalization',
        'assertions':sum(counts.values()),'counts':counts,'anomaly_coefficients':anomaly,
        'python':platform.python_version(),'sympy':s.__version__}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path)
    args=parser.parse_args(); result=run();text=json.dumps(result,indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(text+'\n')
    print(text)
