#!/usr/bin/env python3
"""Optional mpmath diagnostics, not interval certificates or theorem proofs.

The standard-library core computes exact integer moments. This program has no
inputs, uses n<=600, and uses a private mpmath context at 80 decimal digits.
It does not change global precision or Python integer-conversion settings.
"""
from fractions import Fraction
import mpmath
from lengyel_exact import raw_moment_totals


def main():
    mp = mpmath.mp.clone()
    mp.dps = 80
    L = mp.log(2)
    c = [mp.mpf(1), L/6, -L*(16*L*L+45*L-90)/3240,
         L*L*(10*L*L-81*L-270)/6480,
         L*(1792*L**5+32400*L**4+2358405*L**3-
            1281420*L**2-8108100*L-408240)/146966400]
    print('DIAGNOSTICS ONLY: no interval-certified C, K1, K2 or inverse cutoff')
    for n in (100, 200, 400, 600):
        totals = raw_moment_totals(n, 2)
        z = totals[0]
        mean_exact = Fraction(totals[1], z)
        variance_exact = Fraction(totals[2], z)-mean_exact*mean_exact
        mean = mp.mpf(mean_exact.numerator)/mean_exact.denominator
        variance = mp.mpf(variance_exact.numerator)/variance_exact.denominator
        logf = 2*mp.loggamma(n+1)-n*mp.log(2*L)-(1+L/3)*mp.log(n)
        p = sum(value/mp.mpf(n)**j for j, value in enumerate(c))
        corrected = mp.exp(mp.log(z)-logf)/p
        mn = mean-n/(2*L)-mp.log(n)/6+mp.mpf(1)/(12*n)
        vn = variance-n*(1-L)/(4*L*L)+mp.log(n)/12-mp.mpf(1)/(24*n)
        print('n='+str(n), 'C_M4='+mp.nstr(corrected, 24),
              'mean_centered='+mp.nstr(mn, 24),
              'variance_centered='+mp.nstr(vn, 24))
    # A free test K does not pretend to certify the true Lengyel constant.
    beta, K = L/3, mp.mpf(7)
    kappa = 1+mp.log(2*L)/2
    d1, d2 = (1+L)/6, -L*(16*L*L+90*L-90)/3240
    H = lambda x: 2*x*(mp.log(x)-kappa)
    F = lambda x: H(x)-beta*mp.log(x)+mp.log(K)+d1/x+d2/x**2
    for x in (100, 1000, 10000):
        X = mp.mpf(x)
        y = H(X)
        w = mp.lambertw(y/(2*mp.exp(kappa)))
        core = y/(2*w)
        if not mp.almosteq(core, X):
            raise RuntimeError('Lambert core diagnostic failed')
        lam = 2*(1+w)
        v0 = (beta*mp.log(X)-mp.log(K))/lam
        v1 = -(v0*v0-beta*v0+d1)/lam
        v2 = -((2*v0-beta)*v1-v0**3/3+beta*v0*v0/2-d1*v0+d2)/lam
        approximate = X+v0+v1/X+v2/X**2
        root = mp.findroot(lambda z: F(z)-y, (X-1, X+1))
        scaled = (approximate-root)*X**3*mp.log(X)
        print('free_K=7 X='+str(x), 'scaled_inverse_error='+mp.nstr(scaled,24))
    print('DIAGNOSTICS COMPLETED')


if __name__ == '__main__':
    main()
