#!/usr/bin/env python3
"""Exact Bonferroni enclosures and rational asymptotic-error certificates.

All interval endpoints are rational. Decimal displays are rounded outwards.
No guessed recurrence and no floating-point assumption enters a certificate.
"""
from __future__ import annotations
import json
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
from path_forests import stable_moments

ROOT=Path(__file__).resolve().parents[1]


def decimal_bound(q: Q, lower: bool, digits: int=12) -> str:
    with localcontext() as ctx:
        ctx.prec=digits
        ctx.rounding=ROUND_FLOOR if lower else ROUND_CEILING
        return str(Decimal(q.numerator)/Decimal(q.denominator))


def negative_exp_interval(theta: int) -> tuple[Q,Q]:
    # Taylor's alternating series for e^{-1}, followed by monotone squaring.
    lo=sum((Q((-1)**j,factorial(j)) for j in range(102)),Q(0))  # odd degree 101
    hi=lo+Q(1,factorial(102))
    assert 0<lo<hi<1
    return lo**theta,hi**theta


def main() -> None:
    data=json.loads((ROOT/'data'/'coefficients_order16.json').read_text())
    records=[]
    for n in (80,160,320):
        # k=30/31 suffices to certify the displayed scaled residuals.
        moments_by_theta={}
        for theta in (1,2):
            moments=stable_moments(n,2,2,theta,31)
            upper=sum(((-1)**k*moments[k] for k in range(31)),Q(0))
            lower=upper-moments[31]
            assert 0<lower<upper<1
            moments_by_theta[theta]=(lower,upper)
            cs=list(map(Q,data[str(theta)]['c']))
            elo,ehi=negative_exp_interval(theta)
            for M in (4,8,10):
                polynomial=sum((cs[j]/n**j for j in range(M+1)),Q(0))
                assert polynomial>0
                # Residual after removing terms through M, rescaled by n^{M+1}e^theta.
                rlo=(lower/ehi-polynomial)*n**(M+1)
                rhi=(upper/elo-polynomial)*n**(M+1)
                record={'n':n,'theta':theta,'order':M,
                    'probability_lower':str(lower),'probability_upper':str(upper),
                    'scaled_error_lower':str(rlo),'scaled_error_upper':str(rhi),
                    'scaled_error_display':[decimal_bound(rlo,True),decimal_bound(rhi,False)],
                    'next_coefficient':str(cs[M+1]),
                    'bonferroni_cutoff':31}
                records.append(record)
                print(f'n={n:3d}, theta={theta}, M={M:2d}: '
                      f'{record["scaled_error_display"]}, next={cs[M+1]}',flush=True)
    (ROOT/'data'/'bonferroni_certificates.json').write_text(json.dumps(records,indent=2)+'\n')


if __name__=='__main__':
    main()
