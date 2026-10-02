#!/usr/bin/env python3
"""Evaluate the fixed-k forward model or its specified continuous inverse.

Examples:
  python code/evaluate_model.py forward --k 3 --n 80 --order 2
  python code/evaluate_model.py inverse --k 3 --target 1e100 --order 2
Orders 0,1,2 retain the explicitly proved corrections through d_order.
These are asymptotic approximations, not certified finite-target thresholds.
"""
import argparse
from math import factorial, prod
import json
import mpmath as mp


def parameters(k):
    if k < 2:
        raise ValueError('k must be at least two')
    K = mp.mpf(k)
    alpha = (K*K-1)/2
    L = k*mp.log(k+1)
    C = mp.mpf(prod(factorial(j) for j in range(k))) * K**(-K*K/2+K+1) * (K+1)**(k*k-k-1)
    C /= (2*mp.pi)**((K-1)/2) * (K+2)**alpha
    d1 = -(K-1)*(K+1)*(2*K**4+8*K**3+9*K**2+6*K+12)/(12*K*(K+2)**2)
    polynomial = (4*K**12+40*K**11+172*K**10+448*K**9+877*K**8+1342*K**7
                  +1227*K**6+42*K**5-1332*K**4-1968*K**3-2064*K**2-1440*K-576)
    d2 = (K*K-1)*polynomial/(288*K**3*(K+2)**5)
    return alpha, L, C, d1, d2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['forward', 'inverse'])
    parser.add_argument('--k', type=int, required=True)
    parser.add_argument('--order', type=int, choices=[0,1,2], default=2)
    parser.add_argument('--n', type=int)
    parser.add_argument('--target')
    parser.add_argument('--digits', type=int, default=50)
    args = parser.parse_args()
    mp.mp.dps = args.digits + 10
    alpha, L, C, d1, d2 = parameters(args.k)
    if args.mode == 'forward':
        if args.n is None or args.n <= 0:
            parser.error('forward requires --n > 0')
        n = mp.mpf(args.n)
        factor = 1 + (d1/n if args.order >= 1 else 0) + (d2/n**2 if args.order >= 2 else 0)
        value = C*mp.exp(L*n)*n**(-alpha)*factor
        out = {'k': args.k, 'n': args.n, 'correction_order': args.order,
               'forward_approximation': mp.nstr(value, args.digits),
               'normalized_factor': mp.nstr(factor, args.digits)}
    else:
        if args.target is None:
            parser.error('inverse requires --target')
        target = mp.mpf(args.target)
        if target <= 0:
            parser.error('target must be positive')
        argument = -(L/alpha)*(C/target)**(1/alpha)
        if argument < -1/mp.e:
            parser.error('target is below the increasing carrier branch minimum')
        x0 = mp.re(-alpha/L*mp.lambertw(argument, -1))
        value = x0
        if args.order >= 1:
            value -= d1/(L*x0)
        if args.order >= 2:
            ell2 = d2-d1*d1/2
            value += (-ell2/L-alpha*d1/L**2)/x0**2
        out = {'k': args.k, 'target': args.target, 'correction_order': args.order,
               'carrier_inverse': mp.nstr(x0, args.digits),
               'specified_model_inverse_approximation': mp.nstr(value, args.digits)}
    out['qualification'] = 'Fixed-k asymptotic approximation; no certified finite-n remainder or integer threshold'
    print(json.dumps(out, indent=2))

if __name__ == '__main__':
    main()
