#!/usr/bin/env python3
"""Exact algebra and Fabius-density diagnostics for the accompanying article.

No theorem-prover certification is claimed. Exact checks use Fraction/SymPy.
Optional quadrature is floating-point, windowed, and is not a certified value
of the complete Renyi information.
"""
from __future__ import annotations
import argparse
import json
import math
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import mpmath as mp

@lru_cache(maxsize=None)
def moments(n: int) -> tuple[Fraction, ...]:
    """Moments of X=sum_{j>=1} 2^{-j} U_j, U_j uniform on [0,1]."""
    if n < 0:
        raise ValueError('The moment order must be nonnegative.')
    values = [Fraction(1)]
    for k in range(1, n + 1):
        values.append(sum((Fraction(math.comb(k, j), k-j+1)*values[j]
                           for j in range(k)), Fraction()) / (2**k-1))
    return tuple(values)

def expected_power(d: Fraction, n: int, mu: tuple[Fraction, ...]) -> Fraction:
    return sum((math.comb(n,j)*(-1)**j*d**(n-j)*mu[j]
                for j in range(n+1)), Fraction())

def dyadic_density(k: int, n: int) -> Fraction:
    """Exact density at k/2**n. This is a density, NOT the Fabius CDF."""
    if n < 1 or k < 0 or k > 2**n:
        raise ValueError('Require n>=1 and 0<=k<=2**n.')
    k = min(k, 2**n-k)
    if k == 0:
        return Fraction(0)
    if k > 4096:
        raise ValueError('Use a smaller dyadic numerator (this is a tail evaluator).')
    mu = moments(n-1)
    total = sum(((-1)**j.bit_count()*expected_power(Fraction(k-j), n-1, mu)
                 for j in range(k)), Fraction())
    return Fraction(2)**((-n*n+3*n)//2)*total/math.factorial(n-1)

def log_fraction(x: Fraction) -> mp.mpf:
    if x <= 0:
        raise ValueError('A positive fraction is required.')
    return mp.log(x.numerator)-mp.log(x.denominator)

def linear_coefficient(alpha: mp.mpf) -> mp.mpf:
    if alpha <= 2:
        raise ValueError('The supercritical formula requires alpha>2.')
    return alpha*(alpha-2)/(alpha-1)*mp.log(alpha)-(alpha-1)*mp.log(alpha-1)

class TailDensity:
    """Floating-point density with an explicit one-term truncation bound.

    The reported radius is the analytic omitted-term bound; it does not include
    floating-point roundoff. Use dyadic_density for exact arithmetic.
    """
    def __init__(self, target: int = 16):
        if target < 2:
            raise ValueError('target must be at least two')
        self.target = target
        self.coefficients: dict[int, list[mp.mpf]] = {}

    def poly(self, n: int) -> list[mp.mpf]:
        if n not in self.coefficients:
            mu = moments(n)
            self.coefficients[n] = [mp.mpf((-1)**j*math.comb(n,j)*mu[j].numerator)
                                    /mu[j].denominator for j in range(n+1)]
        return self.coefficients[n]

    def log_value(self, x: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
        x = min(x, 1-x)
        if x <= 0:
            return mp.ninf, mp.mpf(0)
        n = max(1, int(mp.ceil(mp.log(self.target/x, 2))))
        k = mp.ldexp(x, n)
        jmax = int(mp.floor(k))
        p = self.poly(n-1)
        value = mp.fsum([(-1)**j.bit_count()*mp.polyval(p,k-j)
                         for j in range(jmax)])
        radius = (k-jmax)**(n-1) if k != jmax else mp.mpf(0)
        if value <= radius:
            raise ArithmeticError('Nonpositive density enclosure: raise precision/target.')
        logpref = mp.mpf(-n*n+3*n)/2*mp.log(2)-mp.loggamma(n)
        return logpref+mp.log(value), radius/(value-radius)

def exact_checks() -> dict:
    import sympy as s
    a,L,theta,c,H,m=s.symbols('a L theta c H m',positive=True)
    alpha=a+1; b=a-1
    quadratic=s.simplify(-s.Rational(1,2)-b+(-alpha*b*b+a**3)/2-a*b/2)
    A=theta/L*(1+s.log(L/(theta*c)))+s.log(H)/L+1-theta/2
    # Linear coefficient of log of the normalized endpoint moment.
    raw=(-theta*L/2+s.log(H)-theta*s.log(c)-theta*s.log(theta)+theta-b*L-A*L
         +theta*(-alpha*b*s.log(b*L)+a*a*s.log(a*L))
         +theta*(alpha*b*s.log(alpha*b)-a*a*s.log(a*a)))
    target=-a*L+theta*(alpha*b*s.log(alpha)-a*a*s.log(a))
    cancellation=s.simplify(s.expand_log(raw-target,force=True))
    lam=s.symbols('lam',positive=True)
    alloc=s.log(lam)+alpha*b*s.log(1-lam)
    optimum=s.simplify(s.diff(alloc,lam).subs(lam,1/a**2))
    mu=moments(25)
    assert mu[1]==Fraction(1,2) and mu[2]-mu[1]**2==Fraction(1,36)
    assert dyadic_density(1,1)==2
    assert dyadic_density(1,2)==1
    assert dyadic_density(1,3)==Fraction(5,36)
    refinements=0
    for n in range(2,10):
        for k in (1,2,3):
            if k < 2**n:
                assert dyadic_density(k,n)==dyadic_density(2*k,n+1)
                refinements+=1
    assert quadratic==0 and cancellation==0 and optimum==0
    return {'quadratic_identity':str(quadratic),'linear_cancellation':str(cancellation),
            'allocation_stationarity':str(optimum),'dyadic_refinement_checks':refinements,
            'known_density_values':True,'mean':'1/2','variance':'1/36'}

def saddle_table() -> list[dict]:
    """Exact dyadic evaluation of a single transformed endpoint integrand."""
    out=[]; L=mp.log(2); alpha=mp.mpf(3); a=alpha-1
    for m in (8,12,16,24,32,48,64,96):
        h=m.bit_length()-1
        # x=2^h*2^(-2m), lambda=1/4, z=3*2^(-(m-h+2)).
        D=(2*m-h)*L; W=D-m*L; lam=mp.mpf(1)/4
        fx=dyadic_density(1,2*m-h)
        fz=dyadic_density(3,m-h+2)
        logA=-L*m*(m+1)/2-mp.loggamma(m)+m*L  # c=1/2
        logM_integrand=(logA-(m+1)*W+(m-1)*mp.log(lam)
                        +alpha*log_fraction(fz)-a*log_fraction(fx))
        point_rate=m*L+logM_integrand/a
        predicted=L*m*m/2+linear_coefficient(alpha)*m
        out.append({'m':m,'point_rate':mp.nstr(point_rate,25),
                    'two_term_prediction':mp.nstr(predicted,25),
                    'residual':mp.nstr(point_rate-predicted,20),
                    'residual_over_log2':mp.nstr((point_rate-predicted)/mp.log(m)**2,18)})
    return out

def windowed_endpoint_quadrature(m: int, nodes: int, target: int = 16) -> dict:
    """Numerical endpoint integral for q=1/2, alpha=3, both endpoints.

    It excludes x>=r/4 and truncates W at a finite upper limit. It therefore
    is an approximation to an endpoint contribution, not a certified full I_3.
    """
    import numpy as np
    if m < 4 or nodes < 8:
        raise ValueError('Require m>=4 and nodes>=8.')
    L=mp.log(2); alpha=mp.mpf(3); a=alpha-1
    density=TailDensity(target)
    center=m*L-mp.log(m)
    lo=mp.log(4); hi=max(lo+1,center+12)
    xs,ws=np.polynomial.legendre.leggauss(nodes)
    lambdas=[(mp.mpf(str(t))+1)/2 for t in xs]
    lweights=[mp.mpf(str(w))/2 for w in ws]
    logs=[]; maxerr=mp.mpf(0)
    logA=-L*m*(m+1)/2-mp.loggamma(m)+m*L
    for t,w in zip(xs,ws):
        W=(lo+hi)/2+(hi-lo)/2*mp.mpf(str(t))
        ww=(hi-lo)/2*mp.mpf(str(w))
        fx,err=density.log_value(mp.exp(-m*L-W)); maxerr=max(maxerr,err)
        common=logA-(m+1)*W-a*fx
        for lam,lw in zip(lambdas,lweights):
            fz,err=density.log_value((1-lam)*mp.exp(-W)); maxerr=max(maxerr,err)
            logs.append(common+(m-1)*mp.log(lam)+alpha*fz+mp.log(ww*lw))
    top=max(logs)
    logM=mp.log(2)+top+mp.log(mp.fsum([mp.exp(v-top) for v in logs]))
    rate=m*L+logM/a
    prediction=L*m*m/2+linear_coefficient(alpha)*m
    return {'m':m,'nodes_each_axis':nodes,'window_W':[mp.nstr(lo,12),mp.nstr(hi,12)],
            'endpoint_rate_estimate':mp.nstr(rate,22),'two_term_prediction':mp.nstr(prediction,22),
            'residual':mp.nstr(rate-prediction,18),
            'max_density_omitted_term_relative_bound':mp.nstr(maxerr,6),
            'certified_full_information':False}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quadrature',type=int,nargs='*',default=[])
    parser.add_argument('--nodes',type=int,default=32)
    parser.add_argument('--dps',type=int,default=100)
    parser.add_argument('--output',type=Path,default=Path(__file__).parent)
    args=parser.parse_args()
    if args.dps < 50:
        parser.error('--dps must be at least 50')
    mp.mp.dps=args.dps
    args.output.mkdir(parents=True,exist_ok=True)
    report={'precision_digits':args.dps,'exact_checks':exact_checks(),
            'saddle_point_diagnostics':saddle_table(),
            'quadrature':[windowed_endpoint_quadrature(m,args.nodes) for m in args.quadrature]}
    name='verification.json' if not args.quadrature else f'quadrature_{args.nodes}.json'
    (args.output/name).write_text(json.dumps(report,indent=2)+'\n')
    # The retained table is sufficient for a PDF-only rebuild.
    if not args.quadrature:
        rows = []
        for row in report['saddle_point_diagnostics']:
            values = [format(float(row[key]), '.8f') for key in
                      ('point_rate', 'two_term_prediction', 'residual')]
            rows.append(str(row['m'])+' & '+' & '.join(values)+r' \\')
        (args.output/'saddle_rows.tex').write_text('\n'.join(rows)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':
    main()
