#!/usr/bin/env python3
"""Floating-point illustration of the q=1 theorem, no external packages.

The mathematical proof is in paper.tex. These checks are not certified bounds,
and finite samples cannot prove an asymptotic statement.
"""
import argparse
from array import array
import csv
import math
from pathlib import Path

GAMMA_E = 0.577215664901532860606512090082402431


def mangoldt_sieve(n):
    """Return Lambda(0),...,Lambda(n); zero outside prime powers."""
    prime = bytearray(b'\x01') * (n + 1)
    prime[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(n) + 1):
        if prime[p]:
            prime[p*p:n+1:p] = b'\x00' * ((n-p*p)//p + 1)
    values = array('d', [0.0]) * (n + 1)
    for p in range(2, n + 1):
        if prime[p]:
            logp = math.log(p)
            a = p
            while a <= n:
                values[a] = logp
                a *= p
    return values


def prefix_sums(values):
    """Kahan-summed prefix arrays for S(x)=sum Lambda/n - sum Lambda/x."""
    harmonic = array('d', [0.0]) * len(values)
    psi = array('d', [0.0]) * len(values)
    h = v = h_err = v_err = 0.0
    for n in range(1, len(values)):
        a = values[n] / n - h_err
        hn = h + a
        h_err = (hn - h) - a
        h = hn
        a = values[n] - v_err
        vn = v + a
        v_err = (vn - v) - a
        v = vn
        harmonic[n], psi[n] = h, v
    return harmonic, psi


def s(x, prefixes):
    assert x >= 1
    h, p = prefixes
    n = math.floor(x)
    return h[n] - p[n] / x


def trivial_sum(x):
    """T(x) in (15). Series avoids cancellation for x not near 1."""
    if x == 1:
        return 1 - math.log(2)
    if not x > 1:
        raise ValueError('x must be >=1')
    y = 1 / x
    if x < 1.5:
        return y * (1 - 0.5 * math.log1p(-y*y) - math.atanh(y)/y)
    z = y*y
    p = y*z
    terms = []
    for m in range(1, 1000):
        v = p / (2*m*(2*m+1))
        terms.append(v)
        if v <= 1e-17 * terms[0]:
            break
        p *= z
    return math.fsum(terms)


def constant(c, prefixes):
    z0 = 2 + GAMMA_E - math.log(4*math.pi)
    inner = s(c, prefixes) - math.log(c) + 1 + GAMMA_E \
        - math.log(2*math.pi)/c + trivial_sum(c)
    return z0 - 2*c/(c+1)*inner


def window(x, c, prefixes):
    a, b = c/(c+1), 1/(c+1)
    w = math.fsum([s(x,prefixes), -a*s(c*x,prefixes),
                   -b*s(x/c,prefixes), (a-b)*math.log(c)])
    corrected = math.sqrt(x) * math.fsum([w, trivial_sum(x),
                       -a*trivial_sum(c*x), -b*trivial_sum(x/c)])
    return w, corrected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-x', type=int, default=500_000)
    parser.add_argument('--c', type=float, default=2.0)
    parser.add_argument('--powers', type=int, nargs='+', default=[2,3,4,5,10])
    parser.add_argument('--out', type=Path, default=Path('samples.csv'))
    args = parser.parse_args()
    if not (1 < args.c <= args.max_x and args.max_x >= 100 and min(args.powers) >= 1):
        parser.error('require 1<c<=max-x, max-x>=100, powers>=1')
    c = args.c
    N = math.ceil(c*args.max_x) + 1
    values = mangoldt_sieve(N)
    pref = prefix_sums(values)
    for x in [1, 1.5, 2, 3.1, 10, 17.7, 50, 100.5]:
        direct = math.fsum(values[n]*(1/n-1/x) for n in range(1, math.floor(x)+1))
        assert math.isclose(s(x,pref), direct, abs_tol=2e-13)
    # Independent arithmetic checks of the balanced multiplier.
    for r in [0.05,0.2,0.5,0.8,0.95]:
        for t in [0,1,14.134725,30.0]:
            import cmath
            z = complex(r,t)
            u = cmath.exp((z-1)*math.log(c))
            p = 1-(c*u+1/u)/(c+1)
            factor = (1-u)*(c*u-1)/((c+1)*u)
            assert abs(p-factor) < 1e-12
            if r == 0.5:
                assert abs(p.imag) < 1e-12 and p.real > 0
    L = constant(c,pref)
    assert L > 0
    print(f'c={c:g}; largest center={args.max_x}; sieve up to {N}')
    print(f'Predicted sharp constant L_1(c) = {L:.15f}')
    if c == 2:
        assert abs(L-0.0625323180445017) < 3e-14
    print('Direct-sum and filter algebra tests passed.')
    print('k  count      max corrected      min corrected      center of max')
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open('w',newline='') as fp:
        writer=csv.writer(fp)
        writer.writerow(['k','n','x','W','sqrt_x_W','corrected_normalized','sharp_bound'])
        for k in args.powers:
            n=1
            points=[]
            while n**k <= args.max_x:
                x=n**k
                if x >= c:
                    w, v = window(x,c,pref)
                    assert abs(v) <= L + 5e-8, (k,n,x,v,L)
                    points.append((v,x))
                    writer.writerow([k,n,x,f'{w:.16g}',f'{math.sqrt(x)*w:.16g}',f'{v:.16g}',f'{L:.16g}'])
                n+=1
            if points:
                mx, xm=max(points)
                mn=min(points)[0]
                print(f'{k:2d} {len(points):6d} {mx:18.12f} {mn:18.12f} {xm:16d}')
            else:
                print(f'{k:2d} no points')
    print('All sampled corrected inequalities satisfied with tolerance 5e-8.')
    print('These are floating-point consistency checks, not a proof of RH or of the limit.')


if __name__ == '__main__':
    main()
