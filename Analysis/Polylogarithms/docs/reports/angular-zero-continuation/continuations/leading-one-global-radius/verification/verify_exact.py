#!/usr/bin/env python3
"""Exact finite replays for the accompanying research article.

Only the Python standard library is required. Rational root brackets are
certificates, using an explicitly proved infinite-series tail bound. Finite
coefficient and moment tests are regression checks, not universal proofs.
No received evidence is overwritten: pass --output-dir to a fresh directory.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json
import sys


def harmonic(n: int, b: int = 1) -> F:
    return sum((F(1, k**b) for k in range(1, n+1)), F(0))


def raw_moment(j: int, b: int) -> F:
    return 2*harmonic(j+1, b)/((j+1)*(j+2))


def central_moment(p: int, b: int) -> F:
    mu=raw_moment(1,b)
    return sum((comb(p,j)*(-mu)**(p-j)*raw_moment(j,b)
                for j in range(p+1)),F(0))


def floor_positive(q: F, digits: int=30) -> str:
    """A nonnegative rational lower bound, printed as an exact fraction."""
    if q <= 0:
        raise AssertionError('expected a strictly positive margin')
    d=10**digits
    return str(F((q.numerator*d)//q.denominator,d))


def inverse_power_bounds(k: int, b: F, digits: int=60) -> tuple[F,F]:
    """Exact bounds for k**(-b), including b=1/2 and 1/4.

    For nonintegral b=p/q with q a power of two, integer square roots give
    floor(D/k**(p/q)) without any floating-point arithmetic.
    """
    if b.denominator==1:
        v=F(1,k**b.numerator)
        return v,v
    q=b.denominator
    if q & (q-1):
        raise ValueError('nonintegral exponent denominator must be a power of two')
    D=10**digits
    N=D**q//k**b.numerator
    r=N
    while q>1:
        r=isqrt(r)
        q//=2
    # Check the certificate inequalities directly, independently of isqrt.
    assert r**b.denominator*k**b.numerator <= D**b.denominator
    assert (r+1)**b.denominator*k**b.numerator > D**b.denominator
    return F(r,D),F(r+1,D)


def angular_interval(b: F, rho: F, eta: F, nmax: int) -> tuple[F,F]:
    """Rigorous rational enclosure of the truncated normalized imaginary part."""
    x=rho*rho*eta
    s=rho*rho
    p0,p1=F(0),F(1)
    hlow,hhigh=F(0),F(0)
    low,high=F(0),F(0)
    for n in range(2,nmax+1):
        clo,chi=inverse_power_bounds(n-1,b)
        hlow+=clo;hhigh+=chi
        p0,p1=p1,2*x*p1-s*p0
        if p1>=0:
            low+=hlow*p1/n; high+=hhigh*p1/n
        else:
            low+=hhigh*p1/n; high+=hlow*p1/n
    return low,high


def tail_bound(rho: F, nmax: int) -> F:
    if not 0<rho<1:
        raise ValueError('the geometric certificate requires 0<rho<1')
    return rho**nmax*(F(nmax)/(1-rho)+rho/(1-rho)**2)


def run(root_inputs: Path) -> dict:
    checks=0
    moment_checks=[]
    for b in range(1,13):
        for p in range(3,32,2):
            value=central_moment(p,b)
            assert (value==0 if b==1 else value>0),(b,p,value)
            checks+=1
            moment_checks.append({'b':b,'order':p,'sign':0 if value==0 else 1})
    # Independent coefficient convolution for atanh(sqrt(z))^2.
    halfshift_checks=0
    for n in range(1,257):
        conv=sum((F(1,(2*j+1)*(2*(n-1-j)+1)) for j in range(n)),F(0))
        odd_h=sum((F(1,2*j+1) for j in range(n)),F(0))
        assert conv==odd_h/n
        lhs_minus=sum((F(2,2*k-1) for k in range(1,n)),F(0))/n
        lhs_plus=sum((F(2,2*k+1) for k in range(1,n)),F(0))/n
        rhs_minus=2*conv-F(4,2*n-1)+F(2,n)
        rhs_plus=2*conv-F(2,n)
        assert lhs_minus==rhs_minus
        assert lhs_plus==rhs_plus
        halfshift_checks+=3
    # Positive integral shifts, with each removable pole cancelled first.
    shift_checks=0
    for m in range(1,13):
        for n in range(1,81):
            lhs=sum((F(1,k+m) for k in range(1,n)),F(0))/n
            rhs=harmonic(n-1)/n+F(1,n*n)-F(1,m*n)
            rhs-=sum((F(1,j*(n+j)) for j in range(1,m)),F(0))
            assert lhs==rhs,(m,n,lhs,rhs)
            shift_checks+=1
    # The local radial coefficient is -2 times the third central moment.
    cubic_checks=0
    for b in range(1,31):
        U=harmonic(2,b); V=harmonic(3,b); W=harmonic(4,b)
        K=U*V/3-W/5-4*U**3/27
        assert K==-2*central_moment(3,b)
        cubic_checks+=1
    brackets=[]
    for entry in json.loads(root_inputs.read_text())['brackets']:
        b=F(entry['b']);rho=F(entry['rho'])
        low=F(entry['lower']); high=F(entry['upper'])
        nmax=int(entry['terms'])
        assert 0<low<high<1
        bound=tail_bound(rho,nmax)
        lo_sum=angular_interval(b,rho,low,nmax)[1]
        hi_sum=angular_interval(b,rho,high,nmax)[0]
        assert lo_sum+bound<0,(entry,'lower sign failed')
        assert hi_sum-bound>0,(entry,'upper sign failed')
        lo_margin=floor_positive(-lo_sum-bound)
        hi_margin=floor_positive(hi_sum-bound)
        assert F(lo_margin)>0 and F(hi_margin)>0
        brackets.append({**entry,'width':str(high-low),
                         'lower_negative_margin_at_least':lo_margin,
                         'upper_positive_margin_at_least':hi_margin,
                         'tail_bound':str(bound),'passed':True})
    return {
      'status':'PASS',
      'method':'Python fractions.Fraction; no floating-point sign decisions',
      'universal_proofs':'article.tex; finite replays do not replace them',
      'counts':{'odd_central_moment_signs':checks,
                'halfshift_coefficient_equalities':halfshift_checks,
                'positive_shift_coefficient_equalities':shift_checks,
                'local_coefficient_equalities':cubic_checks,
                'certified_root_brackets':len(brackets)},
      'moment_checks':moment_checks,'root_brackets':brackets,
    }


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root-inputs',type=Path,
      default=Path(__file__).resolve().parents[1]/'data'/'root-inputs.json')
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    output=args.output_dir/'exact-results.json'
    if output.exists():
        raise FileExistsError(f'Refusing to overwrite {output}')
    result=run(args.root_inputs)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'counts':result['counts']},indent=2))

if __name__=='__main__':
    main()
