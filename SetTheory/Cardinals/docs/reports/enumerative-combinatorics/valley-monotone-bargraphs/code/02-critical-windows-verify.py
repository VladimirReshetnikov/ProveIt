#!/usr/bin/env python3
"""Independent finite checks for valley-monotone compositions.

Python standard library only. Integer arithmetic is exact. These checks do
not certify the analytic theorems or the high-precision numerical constants.
"""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path


def coefficients(N: int, cap: int | None = None,
                 weights: dict[int, int] | None = None,
                 retain: bool = False):
    """Return U_1,D_1 through degree N; optionally retain every level.

    U counts nonempty unimodal compositions; D counts valley-monotone ones.
    weights[j] marks each interior valley plateau of height j.
    """
    if N < 0 or (cap is not None and cap < 1):
        raise ValueError('N must be nonnegative and cap positive')
    weights = weights or {}
    if any(not isinstance(v, int) or v < 0 for v in weights.values()):
        raise ValueError('This exact checker requires nonnegative integer weights')
    top = min(N, cap) if cap is not None else N
    U = [0]*(N+1); D = [0]*(N+1)
    levels = {top+1: (U[:], D[:])} if retain else {}
    for j in range(top, 0, -1):
        w = weights.get(j, 1)
        unext, dnext = U, D
        U = [0]*(N+1)
        for m in range(j, N+1, j): U[m] = 1
        for shift in range(0, N+1, j):
            a = shift//j+1
            for n in range(j+1, N-shift+1):
                U[n+shift] += a*unext[n]
        # den = (1-q^j)^2 - w q^j(1-q^j)U_{j+1}
        den = [0]*(N+1); den[0] = 1
        if j <= N: den[j] -= 2
        if 2*j <= N: den[2*j] += 1
        for n in range(j+1, N-j+1): den[n+j] -= w*unext[n]
        for n in range(j+1, N-2*j+1): den[n+2*j] += w*unext[n]
        # num = q^j(1-q^j) - w q^(2j)U_{j+1} + D_{j+1}
        num = dnext[:]
        if j <= N: num[j] += 1
        if 2*j <= N: num[2*j] -= 1
        for n in range(j+1, N-2*j+1): num[n+2*j] -= w*unext[n]
        nz = [(k, v) for k, v in enumerate(den) if k and v]
        D = [0]*(N+1)
        for n in range(1, N+1):
            value = num[n]
            for k, v in nz:
                if k > n: break
                value -= v*D[n-k]
            D[n] = value
        if retain: levels[j] = (U[:], D[:])
    return (U,D,levels) if retain else (U,D)


def compositions(n: int):
    if n == 0:
        yield ()
        return
    for first in range(1,n+1):
        for tail in compositions(n-first):
            yield (first,)+tail


def valleys(parts: tuple[int,...]) -> list[int]:
    runs = [v for i,v in enumerate(parts) if i == 0 or v != parts[i-1]]
    return [runs[i] for i in range(1,len(runs)-1)
            if runs[i] < runs[i-1] and runs[i] < runs[i+1]]


def run(N: int = 240, brute_N: int = 14):
    U,D,levels = coefficients(N, retain=True)
    oeis = [1,1,2,4,8,15,27,47,79,130,209,330,512,784,1183,
            1765,2604,3804,5504,7898,11240]
    assert [1]+U[1:len(oeis)] == oeis
    assert D[1:16] == [1,2,4,8,16,32,64,128,256,512,1023,
                        2042,4071,8106,16121]
    settings = [(None,{}),(3,{}),(5,{}),(None,{1:2}),
                (None,{1:2,2:3}),(5,{1:2,2:3})]
    expected = {str((cap,ws)): coefficients(brute_N,cap,ws)[1]
                for cap,ws in settings}
    checked = 0
    for n in range(1,brute_N+1):
        totals = Counter()
        for parts in compositions(n):
            vs = valleys(parts)
            if vs != sorted(vs): continue
            for cap,ws in settings:
                if cap is not None and max(parts)>cap: continue
                weight = 1
                for v in vs: weight *= ws.get(v,1)
                totals[str((cap,ws))] += weight
        for key,vals in expected.items():
            assert totals[key] == vals[n], (n,key,totals[key],vals[n])
            checked += 1
    out = Path(__file__).resolve().parent.parent/'data'
    out.mkdir(exist_ok=True)
    payload = {'status':'PASS', 'exact_checks':checked,
               'brute_force_max_area':brute_N, 'max_coefficient_area':N,
               'oeis_A001523_n0_to20_verified':True,
               'D1':[str(x) for x in D],
               'U2':[str(x) for x in levels[2][0]],
               'D2':[str(x) for x in levels[2][1]],
               'notes':'Exact integer finite checks, not a proof assistant certificate.'}
    (out/'exact_checks.json').write_text(json.dumps(payload,indent=2)+'\n')
    print(f'PASS: {checked} independent weighted/capped enumeration checks; '
          f'A001523 terms 0..20; coefficients through {N}.')
    return payload


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--N',type=int,default=240)
    p.add_argument('--brute-N',type=int,default=14)
    a=p.parse_args(); run(a.N,a.brute_N)
