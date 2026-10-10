#!/usr/bin/env python3
"""Numerical diagnostics for the gamma transition remainder at huge N.

No array or sum of length N is formed.  We divide the nonnegative
remainder by the gamma density at t=(log N)/2 before quadrature, and use
stable hypergeometric remainders to avoid cancellation at tiny arguments.
The results are floating-point diagnostics, not interval certificates.
"""

import argparse
import json
from pathlib import Path
import mpmath as mp


def setup():
    d = mp.log(mp.mpf(3)/2)
    lam = 1/d
    p = lam*mp.log(2)
    q = mp.log(3)/mp.log(2)
    b0 = lam*mp.log(q)
    alpha = lam-mp.mpf('.5')
    mu = mp.mpf('.5')-lam+lam*mp.log(2*lam)
    mellin = mp.gamma(-alpha)/2
    psi = mp.digamma(-alpha)
    tri = mp.polygamma(1,-alpha)
    t0 = -(b0-1)*psi-lam/2*(tri+psi*psi)-(b0*b0-b0+mp.mpf(1)/6)/(2*lam)
    amplitude = mellin*mp.sqrt(2*lam/mp.pi)*(2*lam)**(-b0)
    return lam,p,b0,alpha,mu,mellin,t0,amplitude


def stable_r(n, z, x):
    """r_N(z)=G_N(z)-1+Nz, with x=Nz already computed accurately."""
    if z >= 1:
        return n-1
    if z >= mp.mpf('.05'):
        logg = (n-1)*mp.log1p(-z)-mp.log1p(z)
        return mp.expm1(logg)+x
    # a=-log G_N(z)=x+w.  Compute w without subtracting x from a.
    w = z*z/2*((n-1)*mp.hyp2f1(1,2,3,z)-mp.hyp2f1(1,2,3,-z))
    a = x+w
    if a < mp.mpf('.5'):
        exp_remainder = a*a/2*mp.hyp1f1(1,3,-a)
    else:
        exp_remainder = mp.expm1(-a)+a
    return exp_remainder-w


def one(k):
    lam,p,b0,alpha,mu,mellin,t0,amplitude = setup()
    n = mp.power(10,k)
    ell = mp.mpf(k)*mp.log(10)
    length = ell/2
    b = lam*ell+b0

    def integrand(y):
        if y <= -length or not mp.isfinite(y):
            return mp.mpf(0)
        x = mp.exp(-2*y)
        z = x/n
        density_ratio = mp.exp((b-1)*mp.log1p(y/length)-y)
        return density_ratio*(1+mp.sqrt(z))*stable_r(n,z,x)

    points = [-length]+[mp.mpf(y) for y in [-100,-50,-20,-5,0,5,20,50,100,200,500]
                       if y > -length]+[mp.inf]
    integral = mp.quad(integrand, points)
    log_density = -length+(b-1)*mp.log(length)-mp.loggamma(b)
    gamma_prefactor_ratio = mp.exp(log_density+mu*ell+mp.log(ell)/2) / (
        mp.sqrt(2*lam/mp.pi)*(2*lam)**(-b0))
    ratio = gamma_prefactor_ratio*integral/mellin
    conv = lambda z: mp.nstr(z,35)
    return dict(N_power_of_ten=k, logN=conv(ell),
                normalized_remainder=conv(ratio),
                normalized_transition_integral=conv(integral/mellin),
                scaled_first_log_difference=conv(ell*(ratio-1)),
                predicted_first_log_coefficient=conv(t0),
                first_log_approximation=conv(1+t0/ell))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--powers',nargs='+',type=int,default=[8,100,1000,10000,100000,1000000])
    parser.add_argument('--dps',type=int,default=75)
    parser.add_argument('--output',default='transition_remainder_diagnostics.json')
    args=parser.parse_args()
    mp.mp.dps=args.dps
    rows=[]
    for k in args.powers:
        row=one(k)
        rows.append(row)
        print(json.dumps(row),flush=True)
    lam,p,b0,alpha,mu,mellin,t0,amplitude=setup()
    receipt=dict(status='numerical diagnostic, not an interval certificate',
                 decimal_precision=args.dps,mpmath_version=mp.__version__,
                 method='gamma density normalization and positive remainder quadrature',
                 exponent=mp.nstr(mu,50),amplitude=mp.nstr(amplitude,50),
                 first_log_coefficient=mp.nstr(t0,50),rows=rows)
    receipt['normalization']='epsilon_N(b_hat)/(D_0 N^(-mu)/sqrt(log N))'
    receipt['analytic_limit']='1, proved in the article; separate from these numerical diagnostics'
    axis_path=Path(args.output).with_name('axis_large_n_diagnostics.json')
    if axis_path.exists() and any(row['N_power_of_ten']==8 for row in rows):
        axis_rows=json.loads(axis_path.read_text())['rows']
        candidates=[row for row in axis_rows if row['N']==10**8]
        if candidates:
            axis=candidates[0]
            trans=next(row for row in rows if row['N_power_of_ten']==8)
            epsilon=mp.mpf(axis['center_taylor_value'])-mp.mpf(axis['center_taylor_lower'])
            predicted=amplitude*mp.power(10,-8*mu)/mp.sqrt(8*mp.log(10))*mp.mpf(trans['normalized_remainder'])
            receipt['independent_crosscheck']={
                'N':'10^8',
                'method':'compare epsilon to direct axis gamma integral minus exact Taylor leading terms',
                'relative_discrepancy':mp.nstr(abs(epsilon-predicted)/epsilon,12)}
    Path(args.output).write_text(json.dumps(receipt,indent=2)+'\n')


if __name__=='__main__':
    main()
