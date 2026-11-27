#!/usr/bin/env python3
"""Exact filter algebra and illustrative prime-product log data.

Run: python3 experiments.py --output .
Only the optional zeta-zero amplitudes need mpmath. Floating-point prime
logarithms and zeta zeros are illustrations, not certificates of the proof.
"""
import argparse
import bisect
import csv
import math
from pathlib import Path


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            c[i + j] += u * v
    return c


def coeffs(b, k):
    r = math.isqrt(b)
    assert r*r == b and k >= 1
    c = [-b, 1]
    for _ in range(2*k):
        c = mul(c, [-r, 1])
    assert sum(c[j]*b**j for j in range(len(c))) == 0
    # Exact multiplicity >= 2k at r, via ordinary derivatives.
    for l in range(2*k):
        assert sum(c[j]*math.prod(range(j-l+1, j+1))*r**(j-l)
                   for j in range(l, len(c))) == 0
    return c


def primes_to(N):
    sieve = bytearray(b'\x01')*(N+1)
    sieve[0:2] = b'\x00\x00'
    for p in range(2, math.isqrt(N)+1):
        if sieve[p]:
            start=p*p
            sieve[start:N+1:p] = b'\x00'*((N-start)//p+1)
    return [p for p in range(2, N+1) if sieve[p]]


def phi(q):
    return sum(math.gcd(a, q)==1 for a in range(1,q+1))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path('.'))
    ap.add_argument('--max-n', type=int, default=10000)
    a=ap.parse_args()
    assert a.max_n >= 100
    a.output.mkdir(parents=True, exist_ok=True)
    for b in (4,9,16,25):
        for k in range(1,6):
            c=coeffs(b,k)
            # Exact sign at rational midpoints: evaluate polynomial after scaling.
            r=math.isqrt(b); d=len(c)-1
            for t in range(1,16):
                z=16*r+t*(b-r)
                assert sum(cj*z**j*16**(d-j) for j,cj in enumerate(c)) < 0
    print('Exact integer filter identities: passed for b=4,9,16,25; k=1..5.')
    assert coeffs(4,1)==[-16,20,-8,1]
    assert coeffs(9,1)==[-81,63,-15,1]
    print('Two cubic coefficients:', coeffs(4,1), coeffs(9,1))
    ns=sorted(set([10,20,50,100,200,500,1000,2000,5000,10000,a.max_n]))
    ns=[n for n in ns if n<=a.max_n]
    qs=(1,3,5,8,15)
    N=9**3*max(ns)
    ps=primes_to(N)
    print(f'Sieve: {len(ps)} primes <= {N}')
    fields=['q','b','k','n','log_ratio','log_ratio_over_sqrt_n']
    with (a.output/'prime_products.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=fields); wr.writeheader()
        for q in qs:
            psub=[p for p in ps if (p-1)%q==0]
            # Only a few dozen arguments per q; compensate the prefix sum.
            pref=[0.0]; tot=0.0; correction=0.0
            for p in psub:
                y=math.log(p)-correction
                new=tot+y
                correction=(new-tot)-y
                tot=new; pref.append(tot)
            def theta(x): return pref[bisect.bisect_right(psub,x)]
            for b in (4,9):
                c=coeffs(b,1)
                vals=[]
                for n in ns:
                    D=math.fsum(cj*theta(b**j*n) for j,cj in enumerate(c))
                    V=D/math.sqrt(n); vals.append(V)
                    wr.writerow(dict(q=q,b=b,k=1,n=n,log_ratio=f'{D:.12g}',log_ratio_over_sqrt_n=f'{V:.12g}'))
                print(f'q={q:2d}, b={b}: sampled normalized range [{min(vals):.8g}, {max(vals):.8g}]')
    try:
        import mpmath as mp
    except ImportError:
        print('mpmath unavailable; skipped illustrative residue amplitudes.')
        return
    mp.mp.dps=40
    gammas=[mp.im(mp.zetazero(j)) for j in (1,2)]
    print('Approximate first two zeta ordinates:', ', '.join(mp.nstr(g,20) for g in gammas))
    for b in (4,9):
        r=mp.sqrt(b); vals=[]
        for gamma in gammas:
            rho=mp.mpf('0.5')+1j*gamma
            z=mp.exp(rho*mp.log(b))
            v=abs((z-b)*(z-r)**2/rho); vals.append(v)
        print(f'b={b}: first two |P(b^rho)/rho| (multiplicity one): '+', '.join(mp.nstr(v,15) for v in vals))
        print(f'  q=1 cluster bound, assuming listed zeros and no intervening lower frequency: {mp.nstr(mp.sqrt(sum(v*v for v in vals)),15)}')
    print('All floating-point quantities are illustrative; no certified numerical enclosure is claimed.')

if __name__=='__main__':
    main()
