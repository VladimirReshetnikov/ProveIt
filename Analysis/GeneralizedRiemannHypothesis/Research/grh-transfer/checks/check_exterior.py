#!/usr/bin/env python3
"""Certify B_chi>2 outside the two extreme discriminants in Zhao's list.

Requires Python 3, numpy and mpmath. The finite calculation uses integer
weights with explicit error allowances. See the accompanying derivation.
"""
from decimal import Decimal, localcontext
from functools import lru_cache
from math import isqrt
import json
import numpy as np
from mpmath import iv

iv.dps = 35
P = 12
Q = 8000
S = 2**42

def weights():
    # Rows: 1/t, log(t)/t, log(t), log(t)^2, 1/t^2, (log(t)-1)/t^2.
    # The integer divided by S differs from each true entry by < 2/S.
    result = np.zeros((6, (P+1)*Q + 1), dtype=np.int64)
    with localcontext() as ctx:
        ctx.prec = 50
        for k in range(1, result.shape[1]):
            t = Decimal(k)
            h = t.ln()
            vals = (1/t, h/t, h, h*h, 1/(t*t), (h-1)/(t*t))
            result[:,k] = [int(v*S) for v in vals]
    return result

def distinct_factors(n):
    factors = []
    for p in range(2, isqrt(n)+1):
        if n % p == 0:
            factors.append(p)
            n //= p
            if n % p == 0:
                return None
    if n > 1:
        factors.append(n)
    return factors

@lru_cache(None)
def odd_table(p):
    # Legendre symbol for all residues mod p; p is prime.
    table = -np.ones(p,dtype=np.int64)
    k = np.arange(1,p,dtype=np.int64)
    table[(k*k) % p] = 1
    table[0] = 0
    return table

def character(d):
    rad = d // 4 if d % 4 == 0 else d
    if d != (rad if rad % 4 == 1 else 4*rad):
        return None
    factors = distinct_factors(abs(rad))
    if factors is None:
        return None
    q = abs(d)
    n = np.arange(1,q+1,dtype=np.int64)
    chi = np.ones(q,dtype=np.int64)
    dyadic = d
    for p in factors:
        if p > 2:
            chi *= odd_table(p)[n % p]
            dyadic //= p if p % 4 == 1 else -p
    tables = {1:[1], -4:[0,1,0,-1], 8:[0,1,0,-1,0,-1,0,1],
              -8:[0,1,0,1,0,-1,0,-1]}
    last = np.array(tables[dyadic],dtype=np.int64)
    chi *= last[n % len(last)]
    if chi.sum() != 0:
        raise ArithmeticError("Nonzero period sum")
    return chi

def enclosure(d, chi, w):
    q = abs(d)
    n = P*q
    def near(j):
        return int(chi @ w[j,1:n+1].reshape(P,q).sum(axis=0))
    def far(j):
        return int(chi @ w[j,n+1:n+q+1])
    den = 12*q*S
    lnum = 12*q*near(0) - 12*far(2) + 6*q*far(0) + q*q*far(4)
    jnum = 12*q*near(1) - 6*far(3) + 6*q*far(1) + q*q*far(5)
    # One weight error < 2/S. Take absolute values before adding.
    rounding = iv.mpf(2)*(n+1+iv.mpf(q)/2+iv.mpf(q*q)/12)/S
    tail = iv.mpf(1)/(60*P**4)
    signs = iv.mpf([-1,1])
    lval = iv.mpf(lnum)/den + signs*(rounding+tail)
    jsum = iv.mpf(jnum)/den + signs*(rounding+tail*iv.log(n+q))
    if not lval > 0:
        raise ValueError("Undecided sign of L(1,chi)")
    b = iv.log(q/iv.pi) - iv.euler - 2*jsum/lval
    return b if d < 0 else b-2*iv.log(2)

def infinite_bound():
    end = 1000
    total = iv.mpf(0)
    for p in range(2,end+1):
        if all(p % j for j in range(2,isqrt(p)+1)):
            k = p
            while k <= end:
                total += iv.log(p)/(k*k)
                k *= p
    total += (iv.log(end)+1)/end
    if not total < iv.mpf('0.6'):
        raise ArithmeticError("Euler product bound failed")
    bound = (iv.log(Q/iv.pi)-iv.euler-2*total)/3
    if not bound > 2:
        raise ArithmeticError("Conductor cutoff failed")
    return str(total), str(bound)

def main():
    log_deriv, tail_bound = infinite_bound()
    w = weights()
    count = 0
    best = None
    for d in list(range(1-Q,-551)) + list(range(1202,Q)):
        chi = character(d)
        if chi is None:
            continue
        b = enclosure(d,chi,w)
        if not b > 2:
            raise ArithmeticError(f"Unresolved discriminant {d}: {b}")
        # The lower endpoints are exact mp intervals. This finds the lowest
        # certified lower endpoint; it does not compare true enclosed values.
        if best is None or b.a < best[0].a:
            best = (b,d)
        count += 1
    print(json.dumps({"finite_exterior_count":count,
                      "smallest_lower_endpoint_field":best[1],
                      "its_B_interval":str(best[0]),
                      "upper_bound_minus_zeta_log_derivative_at_2":log_deriv,
                      "global_lower_bound_at_8000":tail_bound},indent=2))

if __name__ == "__main__":
    main()
