#!/usr/bin/env python3
"""Exact finite identity tests and illustrative prime-only sampling.
Run: python3 verify.py --limit 200000
No external dependencies. Floating-point diagnostics are not zero certificates.
"""
import argparse
import csv
from fractions import Fraction
from itertools import product
from math import exp, isqrt, log, prod, sqrt, lcm, isclose
from pathlib import Path


def prime_powers(limit):
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b'\x00' * ((limit-p*p)//p+1)
    pairs = []
    for p in range(2, limit + 1):
        if sieve[p]:
            m = p
            while m <= limit:
                pairs.append((m, p))
                m *= p
    return sorted(pairs)


def terms(scales):
    return [(prod(b for b, take in zip(scales, flags) if take), (-1)**sum(flags))
            for flags in product((0, 1), repeat=len(scales))]


def B(q, n, pairs):
    return prod(p**(n-m) for m,p in pairs if m <= n and (m-1)%q == 0)


def exact_ratio(q, n, scales, pairs):
    ratio = Fraction(1)
    for d, sign in terms(scales):
        assert n % d == 0
        ratio *= Fraction(B(q, n//d, pairs))**(sign*d*d)
    return ratio


def direct_ratio(q, n, scales, pairs):
    # Independently collect the ramp contributions, then exponentiate.
    ratio = Fraction(1)
    for m,p in pairs:
        if m > n or (m-1)%q != 0:
            continue
        e = sum(sign*d*max(0,n-d*m) for d,sign in terms(scales))
        ratio *= Fraction(p)**e
    return ratio


def direct_D(q, x, scales, pairs):
    return sum(sign*d*sum(log(p)*max(0.0,1-d*m/x)
                         for m,p in pairs if (m-1)%q==0 and d*m<=x)
               for d,sign in terms(scales))


def prefix(q, limit, pairs):
    weights = [0.0]*(limit+1)
    for m,p in pairs:
        if (m-1)%q==0:
            weights[m] = log(p)
    s, t = [0.0]*(limit+1), [0.0]*(limit+1)
    for i in range(1,limit+1):
        s[i] = s[i-1]+weights[i]
        t[i] = t[i-1]+i*weights[i]
    return s,t


def ramp(x,s,t):
    if x<=1:
        return 0.0
    n=int(x)
    return s[n]-t[n]/x


def filtered(x, scales,s,t):
    return sum(sign*d*ramp(x/d,s,t) for d,sign in terms(scales))


def tests(pairs):
    count=0
    for q in (1,3,5,8):
        for scales in ((2,), (3,), (2,2,2), (2,3,5)):
            b=prod(scales)
            for n in range(b,181,b):
                rat=exact_ratio(q,n,scales,pairs)
                assert rat==direct_ratio(q,n,scales,pairs), (q,n,scales)
                rhs=(log(rat.numerator)-log(rat.denominator))/n
                assert isclose(direct_D(q,n,scales,pairs),rhs,abs_tol=1e-10)
                count+=1
    cumulative_lcm=1
    cumulative_product=1
    for n in range(1,101):
        assert B(1,n,pairs)==cumulative_product
        cumulative_lcm=lcm(cumulative_lcm,n)
        cumulative_product*=cumulative_lcm
    print(f'PASS: {count} exact rational multiscale identities and 100 LCM identities.')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--limit',type=int,default=200000)
    p.add_argument('--samples',type=int,default=1601)
    p.add_argument('--out',type=Path,default=Path(__file__).parent/'sample_fluctuations.csv')
    args=p.parse_args()
    assert args.limit>=200 and args.samples>=2
    pp=prime_powers(args.limit)
    tests(pp)
    # Equally spaced log points, not a certification of limiting means.
    lo,hi=log(60),log(args.limit)
    qs=(1,3,5,8)
    configs=((2,), (2,3,5))
    with args.out.open('w',newline='') as out:
        writer=csv.writer(out)
        writer.writerow(['q','scales','log_x','x','D_over_sqrt_x','positive_part'])
        for q in qs:
            s,t=prefix(q,args.limit,pp)
            for scales in configs:
                vals=[]
                for i in range(args.samples):
                    u=lo+(hi-lo)*i/(args.samples-1)
                    x=min(exp(u),args.limit)
                    v=filtered(x,scales,s,t)/sqrt(x)
                    vals.append(max(v,0))
                    writer.writerow([q,';'.join(map(str,scales)),f'{u:.12g}',f'{x:.12g}',f'{v:.12g}',f'{max(v,0):.12g}'])
                mean=sum(vals)/len(vals)
                print(f'q={q:2d}, b={str(scales):12s}: sampled positive mean={mean:.8g} (finite range only)')
    print('Wrote',args.out.name)

if __name__=='__main__':
    main()
