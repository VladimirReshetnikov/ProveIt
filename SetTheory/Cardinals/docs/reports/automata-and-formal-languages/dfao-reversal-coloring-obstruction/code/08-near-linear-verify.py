#!/usr/bin/env python3
"""Reproducible regression checks for near-linear binary DFAO reversal.
Exact integer tests are separate from Decimal numerical diagnostics.
No third-party dependencies; not a proof-assistant certificate.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
import sys
from decimal import Decimal, localcontext, ROUND_CEILING
from functools import lru_cache
from itertools import product
from pathlib import Path

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


@lru_cache(maxsize=None)
def onto_values(a: int, k: int) -> tuple[int, ...]:
    """onto_values(a,k)[i] counts onto maps to i named labels."""
    powers = [q ** a for q in range(k + 1)]
    return tuple(sum((-1) ** (i-q) * math.comb(i, q) * powers[q]
                     for q in range(i + 1)) for i in range(k + 1))


@lru_cache(maxsize=None)
def biclique(k: int, a: int, b: int) -> int:
    if min(k, a, b) < 1:
        raise ValueError('k,a,b must be positive')
    if a > b:
        return biclique(k, b, a)
    onto = onto_values(a, min(a, k - 1))
    return sum(math.comb(k, i) * onto[i] * (k-i) ** b
               for i in range(1, len(onto)))


def biclique_double(k: int, a: int, b: int) -> int:
    sa, sb = onto_values(a, k), onto_values(b, k)
    return sum(math.comb(k, i) * math.comb(k-i, j) * sa[i] * sb[j]
               for i in range(1, k) for j in range(1, k-i+1))


def split(n: int) -> tuple[int, int]:
    if n < 2:
        raise ValueError('n must be at least 2')
    for a in range(n // 2, 0, -1):
        if math.gcd(a, n-a) == 1:
            return a, n-a
    raise RuntimeError('unreachable')


def threshold(k: int) -> dict[str, int]:
    with localcontext() as ctx:
        ctx.prec = 70
        L = Decimal(8*k).ln()
        S = int((1 + 2*k*L).to_integral_value(rounding=ROUND_CEILING))
        T = 2*S+k if k >= 21 else max(4*k*k, 3*S+k+1, 6*(k+2))
        simple = int((16*k*L).to_integral_value(rounding=ROUND_CEILING))
    return {'k': k, 'S': S, 'T': T, 'simple': simple, 'old_quartic': 3*k**4}


def int_cuberoot(x: int) -> int:
    lo, hi = 0, 1 << ((x.bit_length()+2)//3)
    while lo < hi:
        m = (lo+hi+1)//2
        if m*m*m <= x:
            lo = m
        else:
            hi = m-1
    return lo


@lru_cache(maxsize=None)
def order_bound(r: int) -> int:
    return int_cuberoot(3**r)


def structural(k: int, n: int) -> tuple[int, int]:
    """All compressed graph cases at one (k,n), using exact integers."""
    a, b = split(n)
    target = biclique(k, a, b) - a*b
    require(k**n-target > k**(n-1), f'minimality {k,n}')
    margins = [k**n-k**(n-1)-target,
               (k-1)**2*k**(n-2)-1-target]
    for s in range(2, n+1):
        u, v = split(s)
        B = biclique(k, u, v)
        for d in range(1, n//s+1):
            r = n-d*s
            margin = B**d * k**r - d*u*v*order_bound(r) - target
            if (s,d,r) == (n,1,0):
                require(margin == 0, 'distinguished equality')
            else:
                margins.append(margin)
    for ell in range(2,n+1):
        cycle = (k-1)**ell + (-1)**ell*(k-1)
        for m in range(ell, n+1, ell):
            margins.append(cycle**(m//ell)*k**(n-m)-m*order_bound(n-m)-target)
    require(min(margins) > 0, f'structural comparison failed {k,n}')
    return len(margins), min(margins)


def paired_family(k: int, u: int, v: int) -> int:
    """Exact occupancy construction, with state = occupied pair labels.
    Count label sequences first; multiply each final state by 2**occupied.
    """
    if u > v:
        u, v = v, u
    h = k//2
    counts = [1] + [0]*h
    for side, length in [(0,u),(1,v)]:
        extra = int(k % 2 == 1 and side == 1)
        for _ in range(length):
            nxt = [0]*(h+1)
            for r,c in enumerate(counts):
                nxt[r] += c*(r+extra)
                if r < h:
                    nxt[r+1] += c*(h-r)
            counts = nxt
    return sum(c*2**r for r,c in enumerate(counts))


def palette(k: int, n: int, delta: Decimal = Decimal(0)) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = 65
        return sum(Decimal(math.comb(k,i)) *
                   (Decimal(i*(k-i)).ln()*Decimal(n)/2 +
                    delta*(Decimal(k-i).ln()-Decimal(i).ln())).exp()
                   for i in range(1,k))


def diagnostics(k: int, n: int) -> dict[str, str | int]:
    a,b = split(n)
    with localcontext() as ctx:
        ctx.prec = 65
        scale = Decimal(math.comb(k,k//2)) * (Decimal(k)/2)**n
        ratio = Decimal(biclique(k,a,b)-a*b)/scale
        t = Decimal(n)/Decimal(k*k)
        eps = Decimal(k%2)/2
        theta = sum((-2*t*(Decimal(j)+eps)**2).exp() for j in range(-80,81))
        return {'k':k,'n':n,'n_over_k_squared':str(t),
                'candidate_deficit_scaled':str(ratio),'theta':str(theta),
                'within_this_articles_threshold':n >= threshold(k)['T'],
                'ratio_to_theta':str(ratio/theta)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    parser.add_argument('--full', action='store_true', help='include threshold graph scans')
    args = parser.parse_args()
    report: dict = {'python': platform.python_version(), 'precision_digits':70,
                    'status':'regression checks; not machine-checked proofs'}
    counts = {'counting_identities':0,'literal_colorings':0,'balancing':0,
              'occupancy_subfamilies':0,'occupancy_numeric_bounds':0,
              'imbalance_numeric_bounds':0,'saturation_numeric_bounds':0}
    for k in range(3,13):
        for a in range(1,13):
            for b in range(1,13):
                B = biclique(k,a,b)
                require(B == biclique_double(k,a,b), 'count identity')
                counts['counting_identities'] += 1
                require(paired_family(k,a,b) <= B, 'paired injection')
                counts['occupancy_subfamilies'] += 1
                if b >= a+2:
                    require(B > biclique(k,a+1,b-1), 'balancing')
                    counts['balancing'] += 1
                if k >= 4:
                    with localcontext() as ctx:
                        ctx.prec = 65
                        h=k//2; s=a+b
                        lhs=Decimal(B)
                        rhs=Decimal((k*k)//4)**(Decimal(s)/2) * (
                            Decimal(2).ln()*h*(1-(-Decimal(s)/Decimal(h+1)).exp())).exp()
                        require(lhs >= rhs, 'occupancy numeric inequality')
                        counts['occupancy_numeric_bounds'] += 1
                if k <= 4 and a+b <= 6:
                    brute = sum(not (set(word[:a]) & set(word[a:]))
                                for word in product(range(k),repeat=a+b))
                    require(B == brute,'literal colorings')
                    counts['literal_colorings'] += 1
    for k in list(range(4,31))+[40,60,100]:
        row=threshold(k); S=row['S']; T=row['T']
        for n in [16 if k>=21 else 4*k*k, T, T+1]:
            require(palette(k,n,Decimal(2)) < Decimal('1.5')*palette(k,n), 'imbalance numerical')
            counts['imbalance_numeric_bounds'] += 1
        for s in [S,S+1,S+5]:
            require(Decimal(biclique(k,s//2,s-s//2)) >= Decimal('0.875')*palette(k,s), 'saturation numerical')
            counts['saturation_numeric_bounds'] += 1
    for k in range(4,1001):
        row=threshold(k)
        require(row['simple']>=row['T'],'simple bound')
    report['counts']=counts
    report['thresholds']=[threshold(k) for k in [4,5,6,7,8,10,16,20,21,32,50,100,1000]]
    rows=[]; total=0
    pairs=[(k,n) for k in range(4,13) for n in range(max(7,k+1),61)]
    if args.full:
        pairs += [(k,threshold(k)['T']) for k in [4,5,6,7,8,10,16,20,21,22,30,40]]
    for k,n in pairs:
        c,m=structural(k,n); total+=c
        rows.append({'k':k,'n':n,'comparisons':c,'minimum_strict_margin':str(m)})
    report['structural']={'rows':len(rows),'comparisons':total,'data':rows}
    report['theta_diagnostics']=[diagnostics(k,math.ceil(k*k*t))
        for t in [0.25,0.5,1.0] for k in [20,21,40,41,80,81]]
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'counts':counts,'structural_rows':len(rows),
                      'structural_comparisons':total,'output':str(args.output)},indent=2))

if __name__ == '__main__':
    main()
