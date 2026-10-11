#!/usr/bin/env python3
"""Independent diagnostics for finite Hurwitz multiplication and triple transport.

Exact rational polynomial integrals, direct one-sided subtracted quadrature,
and a separate Mellin evaluation of the colored Tornheim kernel are used.
Floating-point comparisons are diagnostics, not interval certificates.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
CHECKS = []

def rat(x):
    x = F(x)
    return mp.mpf(x.numerator) / x.denominator

def frac(x):
    return x - x.numerator // x.denominator

def record(name, left, right, tolerance):
    err = abs(left - right) / max(mp.mpf(1), abs(right))
    CHECKS.append(dict(name=name, left=mp.nstr(left, 50),
                       right=mp.nstr(right, 50), scaled_error=mp.nstr(err, 12),
                       tolerance=mp.nstr(tolerance, 5), passed=bool(err<tolerance)))
    if not err < tolerance:
        raise AssertionError(CHECKS[-1])

def endpoints(ps, aa):
    out = {}
    for j, (p,a) in enumerate(zip(ps,aa)):
        for k in range(p):
            x = frac((F(k)-a)/p)
            if x in out:
                raise ValueError("Singular grids must be disjoint")
            out[x] = j
    return out

def polynomial_hurwitz_integral(ps, aa, degrees):
    """Exactly integrate product zeta(-degree, {p*x+a})."""
    x = sp.Symbol('x')
    points = sorted(set([F(0),F(1)]) | set(endpoints(ps,aa)))
    total = sp.S.Zero
    for lo, hi in zip(points,points[1:]):
        mid = (lo+hi)/2
        expr = sp.S.One
        for p,a,n in zip(ps,aa,degrees):
            floor = (p*mid+a).numerator // (p*mid+a).denominator
            arg = p*x+sp.Rational(a.numerator,a.denominator)-floor
            expr *= -sp.bernoulli(n+1,arg)/sp.Integer(n+1)
        prim = sp.integrate(sp.expand(expr),x)
        total += prim.subs(x,sp.Rational(hi.numerator,hi.denominator)) \
               - prim.subs(x,sp.Rational(lo.numerator,lo.denominator))
    return sp.factor(total)

def gamma0(x):
    return -mp.digamma(x)

def finite_part_gamma0(ps, aa):
    """Direct ambient-coordinate finite part of a product of gamma_0.

    Each local 1/t term is subtracted in the integrand. This implementation
    does not call the multiplication, bilinear, or Tornheim formulas.
    """
    ep = endpoints(ps,aa)
    points = sorted(set([F(0),F(1)]) | set(ep))
    ans = mp.mpf(0)
    for lo,hi in zip(points,points[1:]):
        h = rat(hi-lo)
        vv = [rat(frac(p*lo+a)) for p,a in zip(ps,aa)]
        if lo not in ep:
            ans += mp.quad(lambda t:mp.fprod(gamma0(v+p*t)
                           for v,p in zip(vv,ps)),[0,h])
            continue
        j = ep[lo]
        others = [k for k in range(len(ps)) if k != j]
        g0 = mp.fprod(gamma0(vv[k]) for k in others)
        g1 = sum((-ps[k]*mp.polygamma(1,vv[k]))*
                 mp.fprod(gamma0(vv[l]) for l in others if l != k)
                 for k in others)
        residue = g0/ps[j]
        def subtracted(t):
            if abs(t) < mp.sqrt(mp.eps):
                return g1/ps[j]+gamma0(1)*g0
            g = mp.fprod(gamma0(vv[k]+ps[k]*t) for k in others)
            return (g-g0)/(ps[j]*t)+gamma0(1+ps[j]*t)*g
        ans += mp.quad(subtracted,[0,h/2,h]) + residue*mp.log(h)
    return ans

def pair_closed(c):
    c=rat(frac(c))
    return mp.stieltjes(1,c)+mp.stieltjes(1,1-c)-2*mp.zeta(2)

def triple_lift_000(ps,aa):
    import itertools
    grids = [[(a+h)/p for h in range(p)] for p,a in zip(ps,aa)]
    logs = [mp.log(p) for p in ps]
    triple = mp.fsum(finite_part_gamma0([1,1,1],list(bs))
                    for bs in itertools.product(*grids))/mp.fprod(ps)
    correction = mp.mpf(0)
    for k in range(3):
        i,j=[v for v in range(3) if v!=k]
        if logs[k]:
            correction += logs[k]*mp.fsum(pair_closed(bj-bi)
                for bi in grids[i] for bj in grids[j])/(ps[i]*ps[j])
    return triple-correction-mp.fprod(logs)

def tornheim_mellin(A,B,C,x,y):
    X=mp.exp(2j*mp.pi*rat(x)); Y=mp.exp(2j*mp.pi*rat(y))
    return mp.quad(lambda t:t**(C-1)*mp.polylog(A,X*mp.exp(-t))*
                   mp.polylog(B,Y*mp.exp(-t)),[0,1,4,mp.inf])/mp.gamma(C)

def check_six_cone():
    import itertools
    ps=[1,1,2]; aa=[F(0),F(1,3),F(1,2)]
    lam=[2,2,2]
    exact=polynomial_hurwitz_integral(ps,aa,[1,1,1])
    rhs=mp.mpf(0)
    cache={}
    for bs in itertools.product(*[[(a+h)/p for h in range(p)]
                                  for p,a in zip(ps,aa)]):
        for k in range(3):
            i,j=[v for v in range(3) if v!=k]
            x,y=frac(bs[i]-bs[k]),frac(bs[j]-bs[k])
            key=tuple(sorted([x,y]))
            if key not in cache:
                cache[key]=tornheim_mellin(2,2,2,*key)
            rhs += -2*mp.re(cache[key])
    rhs *= mp.fprod(ps)/(2*mp.pi)**6
    left=mp.mpf(str(sp.N(exact,mp.mp.dps+5)))
    record('Six-cone Mellin versus exact Bernoulli integral',left,rhs,mp.mpf('1e-30'))
    return str(exact)

def run(skip_mellin=False):
    import itertools
    mp.mp.dps=45
    configurations=[([1,2,3],[F(0),F(1,3),F(1,4)]),
                    ([2,3,1],[F(1,3),F(1,4),F(0)])]
    exact_count=0
    for ps,aa in configurations[:1]:
        for degrees in ([0,0,0],[1,1,1],[0,1,2],[2,0,3]):
            lhs=polynomial_hurwitz_integral(ps,aa,degrees)
            lifted=sum(polynomial_hurwitz_integral([1,1,1],list(bs),degrees)
                       for bs in itertools.product(*[[(a+h)/p for h in range(p)]
                                                 for p,a in zip(ps,aa)]))
            rhs=lifted*sp.prod(sp.Integer(p)**n for p,n in zip(ps,degrees))
            assert sp.simplify(lhs-rhs)==0
            exact_count+=1
    for p,a,x in [(2,F(1,3),mp.mpf('.147')),(5,F(2,7),mp.mpf('.613'))]:
        L=mp.log(p)
        y=mp.frac(p*x+rat(a))
        for n in range(3):
            rhs=mp.fsum(mp.binomial(n,l)*L**(n-l)*
                mp.stieltjes(l,mp.frac(x+rat((a+h)/p)))
                for h in range(p) for l in range(n+1))/p-L**(n+1)/(n+1)
            record(f'Pointwise Stieltjes multiplication p={p}, n={n}',
                   mp.stieltjes(n,y),rhs,mp.mpf('1e-37'))
    for p in [2,3,5]:
        record(f'Ambient mean p={p}',finite_part_gamma0([p],[F(1,7)]),
               -mp.log(p),mp.mpf('1e-34'))
    ps,aa=configurations[0]
    direct=finite_part_gamma0(ps,aa)
    lifted=triple_lift_000(ps,aa)
    record('Triple ambient finite part p=(1,2,3)',direct,lifted,mp.mpf('1e-31'))
    record('Permutation of unequal-frequency factors',
           finite_part_gamma0(*configurations[1]),direct,mp.mpf('1e-34'))
    L2,L3=mp.log(2),mp.log(3)
    unsimplified=L2/3*mp.fsum(pair_closed(c) for c in [F(1,12),F(5,12),F(3,4)]) \
                  +L3/2*mp.fsum(pair_closed(b) for b in [F(1,6),F(2,3)])
    simplified=2*(mp.stieltjes(1)-mp.zeta(2))*(L2+L3) \
        -mp.euler*(6*L2**2+4*L2*L3+3*L3**2) \
        -7*L2**3-7*L2**2*L3-4*L2*L3**2-mp.mpf('1.5')*L3**3
    record('Twelfth-root example lower-term simplification',
           unsimplified,simplified,mp.mpf('1e-37'))
    exact_integral=None if skip_mellin else check_six_cone()
    out=dict(working_decimal_digits=mp.mp.dps, exact_polynomial_checks=exact_count,
             numeric_checks=len(CHECKS), all_passed=all(c['passed'] for c in CHECKS),
             six_cone_exact_rational=exact_integral,
             numerical_checks_are_interval_certificates=False,checks=CHECKS)
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'transport_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--skip-mellin',action='store_true')
    run(parser.parse_args().skip_mellin)
