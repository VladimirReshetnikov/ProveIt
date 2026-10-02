#!/usr/bin/env python3
"""Finite exact consistency checks; these do not replace the analytic audit."""
from collections import defaultdict
from fractions import Fraction as Q
import json


def arrays(n):
    r = {(x, 0): 1 for x in range(2*n+1)}
    b = dict(r)
    b[-1, 0] = 1
    for m in range(1, n+1):
        for x in range(2*m, 2*n+1):
            r[x, m] = r.get((x, m-1), 0) + (m+1)*r.get((x-1, m), 0)
            b[x, m] = (2*b.get((x, m-1), 0)
                       + (m+1)*b.get((x-1, m), 0)
                       - m*b.get((x-3, m-1), 0))
    return r[2*n, n], b[2*n, n]


def path_counts(n, M=None, L=None):
    # State: original horizontal coordinate, vertical coordinate, capped run.
    states = {(0, 0, 0): (Q(1), Q(1))}
    for i in range(1, 3*n+1):
        nxt = defaultdict(lambda: [Q(0), Q(0)])
        for (x, m, run), (ref, alt) in states.items():
            if x < 2*n:
                key = (x+1, m, min(3, run+1))
                nxt[key][0] += (m+1)*ref
                nxt[key][1] += (m+1)*alt
            if m < n and x >= 2*(m+1):
                factor = Q(1)
                if m >= 1 and run >= 3 and (M is None or m < M) and (L is None or i <= L):
                    factor -= Q(1, 2*(m+1)**2)
                key = (x, m+1, 0)
                nxt[key][0] += ref
                nxt[key][1] += factor*alt
        states = nxt
    return states[2*n, n, 0]


def up(i, j):
    return Q(4*(i-j+3), 2*i+j)


def bridge_checks(T):
    forward = [{0: Q(1)}]
    for i in range(1, T+1):
        prev = forward[-1]
        forward.append({j: up(i, j)*prev.get(j-1, 0)+prev.get(j+2, 0)
                        for j in range(i % 3, i+1, 3)})
    p = [None]*(T+1)
    p[T] = {j: Q(int(j == 0)) for j in range(0, T+1, 3)}
    comparisons = 0
    for r in range(T-1, -1, -1):
        p[r] = {s: up(r+1, s+1)*p[r+1].get(s+1, 0)+p[r+1].get(s-2, 0)
                for s in range(r % 3, r+1, 3)}
        for s in range(r % 3, r-2, 3):
            assert p[r][s]/(s+1) >= p[r][s+3]/(s+4)
            comparisons += 1
    assert p[0][0] == forward[T][0]
    for x in range(1, T//3+1):
        for y in range(x+1):
            actual = forward[3*x][3*y]*p[3*x][3*y]/forward[T][0]
            upper = (3*y+1)*forward[3*x][3*y]/forward[3*x][0]
            assert actual <= upper
    return comparisons


def main():
    rows = []
    for n in range(1, 10):
        R, B = arrays(n)
        ref, alt = path_counts(n)
        assert ref == R
        assert alt*2**(n-1) == B
        for M in range(1, 5):
            _, finite_level = path_counts(n, M=M)
            assert Q(0) <= (finite_level-alt)/R <= Q(1, 2*M)
            for L in (0, 3, 7, 12, 3*n):
                _, finite_time = path_counts(n, M=M, L=L)
                assert finite_time >= finite_level
                if L >= 3*n:
                    assert finite_time == finite_level
        rows.append({'n': n, 'R_n': R, 'B_n': B, 'ratio': str(Q(B, 2**(n-1)*R))})
    count = sum(bridge_checks(T) for T in range(3, 37, 3))
    result = {
        'status': 'all exact checks passed',
        'completed_run_counts': rows,
        'bridge_terminals_checked': list(range(3, 37, 3)),
        'adjacent_normalized_bridge_comparisons': count,
        'first_up_weight': str(up(1, 1)),
        'warning': 'Finite checks only; see verdict.md for the analytic proof audit.'
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
