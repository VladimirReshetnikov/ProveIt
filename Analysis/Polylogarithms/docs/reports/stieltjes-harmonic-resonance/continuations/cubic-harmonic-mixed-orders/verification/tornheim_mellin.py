"""Mellin evaluator for the uncolored Tornheim function.

Adapted from verify_rays.py in the preceding ProveIt coincident-directional
report; local split fixed at one, safely within the Jonquiere radius.

Uses a Jonquiere expansion on (0,1), integrated termwise, and the
exponentially convergent incomplete-Gamma expansion on (1,infinity).
No finite-part correlation formula is used in the evaluator.
Numerical checks are not interval certificates or mathematical proofs.
"""
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 65
K = 62
N = 155


def tornheim(a, b, c):
    ga, gb = mp.gamma(1-a), mp.gamma(1-b)
    za = [(-1)**k*mp.zeta(a-k)/mp.factorial(k) for k in range(K+1)]
    zb = [(-1)**k*mp.zeta(b-k)/mp.factorial(k) for k in range(K+1)]
    terms = [ga*gb/(a+b+c-2)]
    terms.extend(ga*zb[k]/(a+c-1+k) for k in range(K+1))
    terms.extend(gb*za[k]/(b+c-1+k) for k in range(K+1))
    terms.extend(za[j]*zb[k]/(c+j+k) for j in range(K+1)
                 for k in range(K+1))
    small = mp.fsum(terms)
    head = [mp.power(j, -a) for j in range(1,N)]
    other = [mp.power(j, -b) for j in range(1,N)]
    large = mp.fsum(
        mp.gammainc(c,k,mp.inf)/mp.power(k,c)
        * mp.fsum(head[j-1]*other[k-j-1] for j in range(1,k))
        for k in range(2,N+1)
    )
    return (small+large)/mp.gamma(c)


def prediction(a,b,c):
    L=mp.log(2*mp.pi)
    B=c*(c*c+a*b-a*a-b*b)/((a+c)*(b+c))
    t0=mp.mpf(1)/4+c/(12*(a+c))+c/(12*(b+c))
    t1=(a+b+2*c)*L/4+B*mp.zeta(-1,derivative=1)
    t2=(2*a*b+c*(a+b))*L*L/4
    t2-=(a*a+b*b+2*c*(a+b)+2*c*c)*mp.zeta(0,derivative=2)/2
    t2+=(a+b+c)*B*mp.zeta(-1,derivative=2)
    return t0,t1,t2


def extrapolate_zero(xs, ys):
    return mp.fsum(y*mp.fprod(-z/(x-z) for z in xs if z != x)
                   for x,y in zip(xs,ys))

