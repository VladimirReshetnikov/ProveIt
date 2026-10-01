#!/usr/bin/env python3
"""Reproduce finite exact tests and tabulated illustrative data.

Run from any directory: python code/verify.py
No third-party packages are required. The assertions check finite statements;
the analytic proof in article.tex is the source of the asymptotic theorems.
"""
from __future__ import annotations
import csv
import gc
import json
from collections import Counter
from fractions import Fraction
from itertools import permutations
from pathlib import Path
from time import perf_counter
from model import (EndpointCounter, avoiders, avoids132, catalans, envelopes,
                   lower_objects, max_jump, proxy)

ROOT=Path(__file__).resolve().parent.parent
DATA=ROOT/'data'
DATA.mkdir(exist_ok=True)
log=[]

def passed(s: str) -> None:
    print('PASS:',s,flush=True)
    log.append('PASS: '+s)


def exact(n: int,m: int) -> int:
    c=EndpointCounter(n,m)
    result=c.count()
    c.T.cache_clear();c.unrestricted.cache_clear()
    return result


def main() -> None:
    start=perf_counter()
    for n in range(8):
        brute={p for p in permutations(range(1,n+1)) if avoids132(p)}
        assert brute==set(avoiders(n))
        assert len(brute)==catalans(n)[n]
    passed('Definition-based permutation test versus Catalan generator, n=0..7')
    checks=0
    for n in range(1,10):
        hist=Counter(max_jump(p) for p in avoiders(n))
        for m in range(n+1):
            assert exact(n,m)==sum(v for k,v in hist.items() if k<=m)
            checks+=1
    passed(f'{checks} endpoint-DP counts versus exhaustive avoiders, n=1..9')
    checks=objects=0
    for n in range(0,11):
        for m in range(2, min(n+3,10)):
            ps=list(lower_objects(n,m)); objects+=len(ps)
            assert len(ps)==len(set(ps)),(n,m,'injection')
            assert all(avoids132(p) and max_jump(p)<=m for p in ps)
            lo,_=envelopes(n,m)
            assert len(ps)==lo[n]
            checks+=1
    passed(f'{checks} lower-construction cases; {objects} generated objects; '
           'avoidance, jump bound, unique decoding, and exact generating counts')
    checks=0
    for n in range(2,25):
        for m in range(2,n+1):
            lo,hi=envelopes(n,m);a=exact(n,m)
            assert lo[n]<=a<=hi[n]<=catalans(n)[n],(n,m)
            checks+=1
    passed(f'{checks} exact coefficientwise sandwiches, n=2..24')
    # Deliberately expose the invalid stronger majorant from the repository.
    # For m=2, 1/(1-x-x^2) has coefficient 3 at n=3; the true count is 5.
    assert exact(3,2)==5
    passed('Regression: the invalid no-append upper bound gives 3 < a_3^(2)=5')
    rows=[]
    for n in (32,64,96,128):
        C=catalans(n)[n]
        for num,den in ((3,5),(1,2),(2,5),(1,3),(1,4)):
            m=n*num//den
            a=exact(n,m);lo,hi=envelopes(n,m)
            r=den//num
            p=float(Fraction(a,C))
            rows.append(dict(n=n,m=m,theta=f'{num}/{den}',exponent=f'{r}/2',
                             count=str(a),catalan=str(C),lower=str(lo[n]),
                             upper=str(hi[n]),probability=p,
                             scaled_probability=n**(r/2)*p))
        gc.collect()
        print(f'DATA: n={n} complete',flush=True)
    with (DATA/'phase_counts.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    passed(f'{len(rows)} exact phase samples through n=128; decimals are rounded')
    crossings=[]
    for n in (64,96):
        C=catalans(n)[n]
        for q in (2,3,4):
            scale=n**(1-1/(2*(q-1)))
            for tnum,tden in ((-1,4),(0,1),(1,4)):
                # Float only selects an integer m; counts below remain exact.
                m=round(n/q+(tnum/tden)*scale)
                if not 2<=m<=n-1:
                    continue
                a=exact(n,m);p=float(Fraction(a,C))
                crossings.append(dict(n=n,m=m,q=q,t=f'{tnum}/{tden}',
                                      count=str(a),probability=p,
                                      order_proxy=proxy(n,m,q),
                                      ratio_to_proxy=p/proxy(n,m,q)))
        gc.collect()
    with (DATA/'crossover_counts.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=crossings[0].keys())
        w.writeheader();w.writerows(crossings)
    passed(f'{len(crossings)} exact crossover samples; proxy is not a limiting function')
    log.append(f'Elapsed seconds: {perf_counter()-start:.3f}')
    (DATA/'verification_log.txt').write_text('\n'.join(log)+'\n')
    print(log[-1])

if __name__=='__main__':
    main()
