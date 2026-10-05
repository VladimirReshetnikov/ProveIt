#!/usr/bin/env python3
"""Optional binary64 diagnostics; these are not certified interval evidence."""
from pathlib import Path
from math import sqrt, pi, log, log1p, fsum, exp
import json

HERE = Path(__file__).resolve().parent
b = pi*sqrt(2/3)
c0 = -log(4*sqrt(3))
phi0 = 9/16


def f(x):
    u = x-1/24
    return b*sqrt(u)-log(4*sqrt(3)*u)+log1p(-1/(b*sqrt(u)))


def fp(x):
    u = x-1/24
    s = sqrt(u)
    return b/(2*s)-1/u+1/(2*b*u*s*(1-1/(b*s)))


def log_ratio(M, phi):
    # Smooth first-Rademacher carriers. No enormous P_M is constructed.
    return (-f(M)+M*((phi+1)*fp(M-0.5)-phi*fp(M+0.5))
            +f((phi+1)*M)-f(phi*M))


def main():
    crossover = []
    for M in [1000, 10000, 100000, 1000000, 10000000, 100000000]:
        lo, hi = .1, 2.0
        if not (log_ratio(M, lo)>0 and log_ratio(M, hi)<0):
            raise RuntimeError('The selected interval does not bracket the equal-weight crossover')
        for _ in range(70):
            mid = (lo+hi)/2
            if log_ratio(M, mid)>0:
                lo = mid
            else:
                hi = mid
        center = (lo+hi)/2
        predicted = phi0+15/(4*b*sqrt(M))*(log(M)+log(36*sqrt(3)/25)-1)
        constant = log(M)+log(36*sqrt(3)/25)-1
        crossover.append({
            'M': M,
            'smooth_leading_carrier_equal_weight_phi': center,
            'first_center_prediction': predicted,
            'center_error_times_M_over_logM_squared': (center-predicted)*M/log(M)**2,
            'log_ratio_remainder_at_phi0_times_sqrtM': (log_ratio(M, phi0)-constant)*sqrt(M),
            'logistic_checks': [{'u':u,
                'actual_log_ratio':log_ratio(M, center+15*u/(4*b*sqrt(M))),
                'target_log_ratio':-u}
                for u in (-2,0,2)],
        })
    p = [int(line.split()[1]) for line in
         (HERE/'partitions_0_10000.txt').read_text().splitlines()]
    sqrt_coefficient = 11*b/24-2/b
    log_coefficient = -11/24-1/(2*b*b)
    # Independent one-order extension, useful for the convergence diagnostic.
    d3 = -b/4608-1/(48*b)-1/(3*b**3)
    next_coefficient = b/24+(-b/48-1/b)/2-2*d3
    finite_product = []
    for M in [100,300,1000,3000,10000]:
        logP = fsum(log(k) for k in p[1:M+1])
        remainder = fsum([logP,-2*b/3*M**1.5,M*log(M),-(1+c0)*M,
                          -sqrt_coefficient*sqrt(M),-log_coefficient*log(M)])
        finite_product.append({'M':M,
            'logP_minus_displayed_terms':remainder,
            'after_subtracting_next_inverse_sqrt_term':remainder-next_coefficient/sqrt(M)})
    out = {'status':'Optional floating diagnostics only, not proof or a rigorous enclosure',
           'crossover':crossover,
           'finite_product':finite_product,
           'next_logP_inverse_sqrtM_coefficient':next_coefficient}
    (HERE/'float_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
