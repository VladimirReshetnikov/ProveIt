#!/usr/bin/env python3
"""Evaluate the paper's asymptotic formulas, not certified finite-n bounds.

The logarithmic parameter calculation supports very large integer n.
The output probabilities are ordinary floating-point approximations.
"""
from __future__ import annotations
import argparse
import json
import math
from typing import Any


def validate(n: int, r: int, p: float) -> None:
    if isinstance(n, bool) or not isinstance(n, int) or n < 2:
        raise ValueError('n must be an integer >= 2')
    if isinstance(r, bool) or not isinstance(r, int) or not 2 <= r <= n:
        raise ValueError('r must be an integer with 2 <= r <= n')
    if not math.isfinite(p) or not 0 < p < 1:
        raise ValueError('p must be finite and strictly between 0 and 1')


def ap_count(n: int, r: int) -> int:
    d = (n-1)//(r-1)
    return n*d-(r-1)*d*(d+1)//2


def log_mean(n: int, r: int, p: float) -> float:
    validate(n,r,p)
    m = ap_count(n,r)
    m_next = ap_count(n,r+1)
    # M_r-p M_{r+1} = M_r [q+p(M_r-M_{r+1})/M_r].
    # This positive representation avoids cancellation at p close to 1.
    return r*math.log(p)+math.log(m)+math.log((1-p)+p*((m-m_next)/m))


def constants(p: float) -> dict[str,float]:
    if not math.isfinite(p) or not 0 < p < 1:
        raise ValueError('p must be finite and strictly between 0 and 1')
    a=-math.log(p);q=1-p
    h=5/6-math.pi**2/18
    c=2*q*h/p
    result = dict(H=h,c_p=c,
                  normalized_error_liminf=16*c/q**2*math.exp(-2*a/q),
                  normalized_error_limsup=16*c/(a*a*math.exp(2)))
    if not all(math.isfinite(v) for v in result.values()):
        raise ValueError('p is too extreme for this floating-point evaluator')
    return result


def lattice_phi(p: float, theta: float) -> float:
    constants(p)  # Validate p.
    if not math.isfinite(theta):
        raise ValueError('theta must be finite')
    theta %= 1
    a=-math.log(p)
    j=math.floor(theta-math.log(2)/a)
    log_x=a*(theta-j)
    def f_from_log(y: float) -> float:
        if y > 700:  # x is huge and x^2 exp(-x) underflows.
            return 0.0
        x=math.exp(y)
        return math.exp(2*y-x)
    return max(f_from_log(log_x),f_from_log(log_x-a))


def evaluate(n: int, r: int, p: float) -> dict[str,Any]:
    lm=log_mean(n,r,p)
    cs=constants(p)
    # If lambda > 1000, both reported approximations round to zero in
    # the intended fixed-p asymptotic use. Keep log(lambda) in the output.
    if lm > math.log(1000):
        poisson=corrected=0.0
        lam=None
    else:
        lam=math.exp(lm)
        poisson=math.exp(-lam)
        # Evaluate correction in log form to avoid large-n intermediate products.
        log_extra=-lam+math.log(cs['c_p'])+2*lm+2*math.log(r)-math.log(n)
        extra=math.exp(log_extra) if log_extra > -745 else 0.0
        corrected=poisson+extra
    L=math.log(n);a=-math.log(p)
    t=(2*L-math.log(L)+math.log((1-p)*a/4))/a
    return dict(n=str(n),r=r,p=p,log_lambda_exact=lm,lambda_exact=lam,
                poisson_avoidance=poisson,corrected_avoidance=corrected,
                lattice_phase=t%1,lattice_phi=lattice_phi(p,t%1),
                **cs,
                warning='Asymptotic formulas only; no certified finite-n error bar. '
                        'A null lambda means its direct float value was omitted.')


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('r',type=int)
    parser.add_argument('--p',type=float,default=0.5)
    args=parser.parse_args()
    try:
        result=evaluate(args.n,args.r,args.p)
    except (ValueError,OverflowError) as exc:
        parser.error(str(exc))
    print(json.dumps(result,indent=2,allow_nan=False))

if __name__=='__main__':
    main()
