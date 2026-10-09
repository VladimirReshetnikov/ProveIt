#!/usr/bin/env python3
"""High-precision evaluation of the local four-cycle extremal branch.

These numerical evaluations are diagnostics, not interval certificates and not
proofs of a globally valid numerical threshold for the local theorem.
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from pathlib import Path
import mpmath as mp

@dataclass(frozen=True)
class Endpoint:
    t: object
    sign: int
    u: object
    v: object
    q: object
    value: object
    residual: object

    def as_dict(self, digits: int = 45) -> dict:
        # Preserve precision in the cancellation-sensitive remainder, even
        # when the caller is outside the solver's workdps context.
        with mp.workdps(max(mp.mp.dps, digits + 20)):
            out = {k: mp.nstr(getattr(self, k), digits)
                   for k in ('t', 'u', 'v', 'q', 'value', 'residual')}
            out['sign'] = self.sign
            out['normalized_remainder_after_t5'] = mp.nstr(
                (self.value - expansion(self.t, self.sign, 5))/self.t**6, digits)
            return out

def expansion(t, sign: int = -1, order: int = 5):
    t = mp.mpf(t)
    if sign not in (-1, 1):
        raise ValueError('sign must be -1 or +1')
    terms = {1: t/4, 3: t**3/4, 4: -sign*t**4/4,
             5: -t**5/8, 6: sign*3*t**6/4}
    return sum(v for k, v in terms.items() if k <= order)

def solve_endpoint(t, sign: int = -1, dps: int = 70) -> Endpoint:
    if sign not in (-1, 1):
        raise ValueError('sign must be -1 or +1')
    if dps < 35:
        raise ValueError('Use at least 35 decimal digits')
    with mp.workdps(dps):
        t = mp.mpf(t)
        if not 0 < t <= mp.mpf('0.25'):
            raise ValueError('Numerical implementation is restricted to 0 < t <= 0.25; this is not a certified theorem radius.')
        def equations(V, X, H):
            v, u, q = t*V, t**3*X, mp.mpf('.5')+t**2*H
            s = mp.sqrt(q*(1-q))
            norm = V**4 + 4*t**2*(1+sign*v+v*v)*X*X + 2*t**8*X**4-1
            ratio = (q*(v**3+(sign+2*v)*u*u)-s*u*(1+sign*v+v*v+u*u))/t**3
            masses = (u*q*(3-4*q)+v*s*(1-2*q))/t**3
            return norm, ratio, masses
        initial = (1-t*t+sign*t**3+mp.mpf('2.5')*t**4,
                   1-sign*t-2*t*t+7*sign*t**3,
                   mp.mpf('.5')-sign*t/2-t*t+mp.mpf('3.5')*sign*t**3)
        V, X, H = mp.findroot(equations, initial, tol=mp.mpf(10)**(-dps+15), maxsteps=100)
        residual = max(abs(z) for z in equations(V, X, H))
        if residual > mp.mpf(10)**(-dps+20):
            raise ArithmeticError('Stationarity residual too large')
        v, u, q = t*V, t**3*X, mp.mpf('.5')+t*t*H
        val = 2*q*mp.sqrt(q*(1-q))*u+q*(1-q)*v
        return Endpoint(+t, sign, +u, +v, +q, +val, +residual)

def block_matrix(e: Endpoint, p='0.5', q=None):
    p = mp.mpf(p)
    q = e.q if q is None else mp.mpf(q)
    if not (0 < p < 1 and 0 < q < 1):
        raise ValueError('p and q must lie in (0,1)')
    s = mp.sqrt(q*(1-q))
    f = [(1-q)/s, -q/s]
    return [[p*(1+e.sign*(e.u*(x+y)+e.v*x*y)) for y in f] for x in f]

def rational_parameter(r, sign=-1, dps=70):
    """Independent local parametrization by r=sqrt(q/(1-q))."""
    if sign not in (-1, 1):
        raise ValueError('sign must be -1 or +1')
    if dps < 35:
        raise ValueError('Use at least 35 decimal digits')
    with mp.workdps(dps):
        r = mp.mpf(r)
        if not (1 < r < mp.sqrt(3)):
            raise ValueError('Need 1 < r < sqrt(3)')
        k = (r*r-1)/(r*(3-r*r))
        A = r*(1+2*k*k)-k*(1+k*k)
        B = sign*(r*k*k-k)
        if A <= 0:
            raise ValueError('Parameter outside implemented local branch')
        v = 2*k/(mp.sqrt(B*B+4*A*k)+B)
        u = k*v
        q = r*r/(1+r*r)
        t = (v**4+4*(1+sign*v+v*v)*u*u+2*u**4)**mp.mpf('.25')
        val = 2*q*mp.sqrt(q*(1-q))*u+q*(1-q)*v
        return Endpoint(+t,sign,+u,+v,+q,+val,mp.mpf('0'))

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--t', default='0.1')
    ap.add_argument('--sign', type=int, choices=(-1,1), default=-1)
    ap.add_argument('--dps', type=int, default=70)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    result = solve_endpoint(args.t, args.sign, args.dps)
    text = json.dumps(result.as_dict(), indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text+'\n')
    print(text)

if __name__ == '__main__':
    main()
