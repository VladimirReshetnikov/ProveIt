#!/usr/bin/env python3
"""Illustrative numerical tests of the gamma-power series asymptotic.
No floating point computation is required by the theorem.
Run with Python 3 and mpmath (tested with 60 decimal digits).
"""
import json
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 60
chi4 = [0, 1, 0, -1]
chi5 = [0, 1, -1, -1, 1]

# All evaluations are at positive real s; no zero computations or RH assumptions.
def log_complete(u, kind):
    s = u + mp.mpf('0.5')
    if kind == 'zeta':
        return (mp.log(s*(s-1)/2) - s/2*mp.log(mp.pi)
                + mp.loggamma(s/2) + mp.log(mp.zeta(s)))
    q, a, chi = (4, 1, chi4) if kind == 'beta' else (5, 0, chi5)
    c = (s+a)/2
    return c*mp.log(q/mp.pi) + mp.loggamma(c) + mp.log(mp.dirichlet(s, chi))

def family(r, s, j):
    d = r+s+j
    kappa = Fraction(7*r+s-j, 4)
    alpha = mp.mpf(2)/d
    qstar = mp.exp((s*mp.log(4)+j*mp.log(5))/d)
    b0 = mp.pi*d/qstar
    pred = mp.mpf(kappa.numerator)/kappa.denominator-mp.mpf('0.5')
    def logterm(n):
        u = alpha*n
        return (n*mp.log(b0)-mp.loggamma(n+1)
                + sum(m*log_complete(u, kind) for m,kind in
                      [(r,'zeta'),(s,'beta'),(j,'chi5')] if m))
    # Normalization and the factor two are constant and cancel in slope estimates.
    rows=[]
    for n in [32,128,512,2048]:
        slope=(logterm(2*n)-logterm(n))/mp.log(2)
        rows.append({'n':n,'slope':mp.nstr(slope,15),
                     'error':mp.nstr(slope-pred,8)})
    assert abs(slope-pred) < mp.mpf('0.02')
    assert (kappa < Fraction(-1,2)) == (j>7*r+s+2)
    return {'counts_zeta_beta_chi5':[r,s,j], 'd':d,
            'kappa':str(kappa), 'b0':mp.nstr(b0,18),
            'endpoint_attained':kappa<Fraction(-1,2),
            'predicted_series_power':str(kappa-Fraction(1,2)),
            'dyadic_slopes':rows}

if __name__ == '__main__':
    ratio = mp.exp(-3*mp.pi/5)
    geometric_tail = ratio/(1-ratio)
    assert geometric_tail < 1
    examples=[(1,0,0),(0,1,0),(1,1,0),(0,0,1),(0,0,2),
              (0,0,3),(1,0,9),(1,0,10)]
    print(json.dumps({'purpose':'illustration, not a proof certificate',
                      'precision_decimal_digits':mp.mp.dps,
                      'chi5_relative_tail_upper_bound':mp.nstr(geometric_tail,18),
                      'examples':[family(*x) for x in examples]},indent=2))
