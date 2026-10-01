"""Exact finite checks, not proofs of asymptotic results.

The endpoint-threshold recurrence is due to Mayama--Akita. This implementation
uses that recurrence without the unrestricted-state shortcut in ProveIt's
05-macroscopic-deficits-model.py (pinned source described in SOURCES.md).
All counts and generating-function coefficients are exact integers/Fractions.
"""
from __future__ import annotations
import argparse
import json
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
from math import comb
from pathlib import Path
from time import perf_counter


def catalan(n: int) -> int:
    return comb(2*n, n)//(n+1)


@lru_cache(None)
def avoiders(n: int) -> tuple[tuple[int, ...], ...]:
    if n < 0:
        raise ValueError('n must be nonnegative')
    if n == 0:
        return ((),)
    return tuple(tuple(x+b for x in left)+(n,)+right
                 for b in range(n) for left in avoiders(n-b-1)
                 for right in avoiders(b))


def avoids132(p: tuple[int, ...]) -> bool:
    return not any(p[i] < p[k] < p[j]
                   for i in range(len(p)) for j in range(i+1, len(p))
                   for k in range(j+1, len(p)))


def max_jump(p: tuple[int, ...]) -> int:
    return max((abs(x-y) for x, y in zip(p, p[1:])), default=0)


class EndpointCounter:
    def __init__(self, N: int, m: int):
        if N < 1 or m < 0:
            raise ValueError('Require N >= 1 and m >= 0')
        self.m = m
        self.H = [[1]]
        for n in range(1, N+1):
            row, running = [], 0
            for j in range(n):
                running += (j+1)*comb(2*n-j-2, n-1)//n
                row.append(running)
            assert running == catalan(n)
            self.H.append(row)
        self.T = lru_cache(None)(self._state)

    def h(self, n: int, u: int) -> int:
        if u < 0:
            return 0
        return self.H[n][min(u, n-1)] if n else 1

    def _state(self, n: int, u: int, v: int) -> int:
        if min(u, v) < 0:
            return 0
        if n == 1:
            return 1
        u, v = min(u, n-1), min(v, n-1)
        total = self.T(n-1, u-1, self.m-1)
        for k in range(1, min(self.m, n-1, v)+1):
            c = 1 if k == 1 else self.h(k-1, u-1)
            if c:
                total += c*self.T(n-k, min(self.m-k, n-k-1),
                                  min(v-k, n-k-1))
        return total

    def count(self, n: int) -> int:
        return self.T(n, n-1, n-1)


def distributions(N: int) -> dict[int, list[int]]:
    """hist[n][d] = number of size-n avoiders with deficit d."""
    hist = {n: [0]*(n+1) for n in range(1, N+1)}
    last = [0]*(N+1)
    for m in range(N):
        counter = EndpointCounter(N, m)
        for n in range(max(1, m+1), N+1):
            count = counter.count(n)
            assert count >= last[n]
            hist[n][n-m] = count-last[n]
            last[n] = count
        counter.T.cache_clear()
    for n, row in hist.items():
        assert sum(row) == catalan(n)
    return hist


def mul(a: list[F], b: list[F], N: int) -> list[F]:
    return [sum((a[j]*b[k-j] for j in range(k+1)), F(0))
            for k in range(N+1)]


def square_root(a: list[F], N: int) -> list[F]:
    if a[0] != 1:
        raise ValueError('This exact routine requires constant term one')
    r = [F(1)] + [F(0)]*N
    for k in range(1, N+1):
        r[k] = (a[k]-sum((r[j]*r[k-j] for j in range(1, k)), F(0)))/2
    return r


def pgf_coefficients(N: int) -> list[F]:
    if N < 1:
        raise ValueError('N must be positive')
    s = square_root([F(1), F(-1)]+[F(0)]*(N-1), N)
    r = square_root([(F(i == 0)+s[i])/2 for i in range(N+1)], N)
    s2 = mul(s, s, N)
    s2r = mul(s2, r, N)
    q = [4*F(i == 0)+8*s[i]+3*s2[i]-s2r[i] for i in range(N+1)]
    num = mul([F(i == 0)-s[i] for i in range(N+1)], q, N)
    plus = [F(i == 0)+s[i] for i in range(N+1)]
    den = [4*x for x in mul([F(i == 0)+2*s[i] for i in range(N+1)],
                            mul(plus, plus, N), N)]
    g = [F(0)]*(N+1)
    for k in range(N+1):
        g[k] = (num[k]-sum((den[j]*g[k-j] for j in range(1, k+1)), F(0)))/den[0]
    assert g[0] == 0 and g[1] == F(7, 48)
    assert all(x > 0 for x in g[1:]) and sum(g) < 1
    assert mul(den, g, N) == num
    return g


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-n', type=int, default=64)
    ap.add_argument('--pgf-terms', type=int, default=128)
    args = ap.parse_args()
    if args.max_n < 10:
        ap.error('--max-n must be at least 10 for the documented checks')
    out = Path(__file__).resolve().parent.parent/'data'
    out.mkdir(exist_ok=True)
    start = perf_counter()
    # Independent definition-based check of the Catalan construction.
    direct_checked = 0
    for n in range(1, 8):
        direct = {p for p in permutations(range(1, n+1)) if avoids132(p)}
        assert direct == set(avoiders(n))
        direct_checked += len(direct)
    hist = distributions(args.max_n)
    enumerated = 0
    for n in range(1, 11):
        perms = avoiders(n)
        assert len(perms) == catalan(n) and len(set(perms)) == len(perms)
        raw = Counter(n-max_jump(p) for p in perms)
        assert hist[n] == [raw[d] for d in range(n+1)]
        enumerated += len(perms)
    # Check every endpoint state as well, independently, for n <= 7.
    endpoint_checks = 0
    for n in range(1, 8):
        for m in range(n):
            ec = EndpointCounter(n, m)
            relevant = [p for p in avoiders(n) if max_jump(p) <= m]
            for u in range(n):
                for v in range(n):
                    brute = sum(n-p[0] <= u and n-p[-1] <= v for p in relevant)
                    assert ec.T(n, u, v) == brute
                    endpoint_checks += 1
            ec.T.cache_clear()
    coeff = pgf_coefficients(args.pgf_terms)
    (out/'exact_distributions.json').write_text(json.dumps(hist, indent=2)+'\n')
    (out/'pgf_coefficients.json').write_text(json.dumps([str(x) for x in coeff], indent=2)+'\n')
    result = {'status': 'PASS', 'max_n_exact_counts': args.max_n,
              'definition_based_avoiders_through_7': direct_checked,
              'generated_avoiders_through_10': enumerated,
              'endpoint_state_equalities': endpoint_checks,
              'pgf_coefficients_checked': args.pgf_terms+1,
              'elapsed_seconds': round(perf_counter()-start, 3),
              'scope': 'Finite regression checks only; no asymptotic proof is machine-verified.'}
    (out/'exact_checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
