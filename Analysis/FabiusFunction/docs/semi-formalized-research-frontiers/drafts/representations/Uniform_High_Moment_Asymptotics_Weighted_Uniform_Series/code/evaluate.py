#!/usr/bin/env python3
"""Evaluate fixed-order geometric moment asymptotics without O(n^2) recurrence.

Outputs are arbitrary-precision numerical approximations, not interval certificates.
Use --reference only for moderate n: that independent recurrence costs O(n^2).
"""
from __future__ import annotations
import argparse
import json
import mpmath as mp
import sympy as sp
from coefficients import saddle_coefficients
from moments import geometric_stats, solve_saddle, log_saddle_carrier, geometric_moments


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, required=True)
    parser.add_argument('--q', default='0.5', help='geometric ratio in (0,1)')
    parser.add_argument('--order', type=int, choices=range(4), default=1)
    parser.add_argument('--digits', type=int, default=80)
    parser.add_argument('--reference', action='store_true')
    args = parser.parse_args()
    if args.n < 2 or args.digits < 30:
        parser.error('n must be at least 2 and digits at least 30')
    mp.mp.dps = args.digits
    q, n = mp.mpf(args.q), args.n
    if not mp.isfinite(q) or not 0 < q < 1:
        parser.error('q must be finite and in (0,1)')
    order = max(2, 2*args.order+2)
    t, stats = solve_saddle(n, lambda x: geometric_stats(x,q,order))
    rho,b,coeff = saddle_coefficients(args.order)
    symbols = [rho]+[b[r] for r in sorted(b)]
    values = [stats.cumulants[2]/n]+[mp.factorial(r-1)+stats.cumulants[r]/n for r in sorted(b)]
    contributions = [sp.lambdify(symbols,c,'mpmath')(*values)/mp.mpf(n)**j for j,c in enumerate(coeff)]
    factor = mp.fsum(contributions)
    if factor <= 0:
        raise RuntimeError('correction factor is nonpositive; n is outside a useful approximation regime')
    logmoment = log_saddle_carrier(n,t,stats)+mp.log(factor)
    fmt=lambda x:mp.nstr(x,args.digits-10)
    result = {'n':n,'q':args.q,'order':args.order,'decimal_working_precision':args.digits,
              'saddle':fmt(t),'saddle_equation_residual':fmt(t-stats.cumulants[1]-n),
              'mu_at_saddle':fmt(stats.cumulants[1]),'variance_at_saddle':fmt(stats.cumulants[2]),
              'correction_contributions':[fmt(c) for c in contributions],
              'log_moment_approximation':fmt(logmoment),
              'head_factors':stats.head_terms,'Bernoulli_tail_terms':stats.tail_terms,
              'status':'fixed-order asymptotic approximation; no numerical remainder or rounding certificate'}
    if q==mp.mpf('0.5'):
        result['log_Fabius_dyadic_value_approximation']=fmt(logmoment-n*(n-1)*mp.log(2)/2-mp.loggamma(n+1))
    if args.reference:
        ref=geometric_moments(n,q)[-1]
        result['independent_log_moment_reference']=fmt(mp.log(ref))
        result['relative_ratio_error_reference_over_approximation_minus_one']=fmt(mp.expm1(mp.log(ref)-logmoment))
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
