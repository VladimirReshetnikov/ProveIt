#!/usr/bin/env python3
"""Exact independent checks for the compacted-path finite-state kernel.
No third-party dependencies. The brute-force routine enumerates labelled paths
without memoization; the other checks use arbitrary-precision integer arithmetic.
"""
from collections import defaultdict
import json


def four_state(N):
    d = defaultdict(lambda: (0, 0, 0, 0))
    d[0, 0] = (1, 0, 0, 0)
    for x in range(N + 1):
        for y in range(x + 1):
            if x == y == 0:
                continue
            Z, A, B, C = d[x - 1, y] if x else (0, 0, 0, 0)
            hz = 0
            ha = Z + A + B + C
            hb = y * (Z + A) + max(y - 1, 0) * (B + C)
            hc = B + C
            vz, va, vb, vc = d[x, y - 1] if y else (0, 0, 0, 0)
            d[x, y] = (vz + va + vb, ha, hb, hc)
    return d


def three_state(N):
    d = defaultdict(lambda: (0, 0, 0))
    d[0, 0] = (1, 0, 0)
    for x in range(N + 1):
        for y in range(x + 1):
            if x == y == 0:
                continue
            E, B, C = d[x - 1, y] if x else (0, 0, 0)
            ve, vb, vc = d[x, y - 1] if y else (0, 0, 0)
            d[x, y] = (E+B+C+ve+vb, y*E+max(y-1,0)*(B+C), B+C)
    return d


def signed(N):
    c = defaultdict(int)
    for x in range(N + 1):
        c[x, 0] = 1
        for y in range(1, x + 1):
            c[x, y] = c[x, y-1] + (y+1)*c[x-1, y] - (y-1)*c[x-2, y-1]
    return c


def run_weight(y, k):
    if k == 0:
        return 1
    if k == 1:
        return y+1
    return (y*y+y+1)*(y+1)**(k-2)


def renewal(N):
    # a[x,y] counts paths ending with V, plus the empty path.
    a = defaultdict(int)
    a[0, 0] = 1
    for y in range(N):
        for x in range(y+1, N+1):
            a[x, y+1] = sum(a[x-k, y]*run_weight(y,k) for k in range(x-y+1))
    return a


def brute(N):
    d = defaultdict(lambda: [0, 0, 0, 0])
    visited = rejected_vertical = 0
    def visit(x, y, trailing_labels):
        nonlocal visited, rejected_vertical
        visited += 1
        if not trailing_labels:
            state = 0
        elif trailing_labels[-1] == 1:
            state = 1
        elif len(trailing_labels) == 2 and trailing_labels[0] == trailing_labels[1]:
            state = 3
        else:
            state = 2
        d[x, y][state] += 1
        if x < N:
            for label in range(1, y+2):
                visit(x+1, y, (trailing_labels + (label,))[-2:])
        if y < x:
            if state == 3:
                rejected_vertical += 1
            else:
                visit(x, y+1, ())
    visit(0,0,())
    return d, visited, rejected_vertical


def main():
    N = 100
    d4, d3, c, a = four_state(N), three_state(N), signed(N), renewal(N)
    for x in range(N+1):
        for y in range(x+1):
            Z,A,B,C = d4[x,y]
            assert (Z+A,B,C) == d3[x,y]
            assert Z+A+B+C == c[x,y]
            assert C == y*c[x-2,y]
            assert B+C == y*c[x-1,y]
            if y:
                assert Z == a[x,y]
                assert Z == c[x,y-1]-(y-1)*c[x-2,y-1]
            if x == y:
                assert A == B == C == 0
                assert a[x,y] == c[x,y]
    b, visited, rejected = brute(7)
    for x in range(8):
        for y in range(x+1):
            assert tuple(b[x,y]) == d4[x,y]
    out = {
        'exact_recurrence_max_n': N,
        'exact_cells_checked': (N+1)*(N+2)//2,
        'brute_force_max_n': 7,
        'brute_force_accepted_prefixes': visited,
        'brute_force_rejected_V_moves': rejected,
        'diagonal_counts_n_0_through_12': [c[n,n] for n in range(13)],
        'n_7_state_row': {str(y): d4[7,y] for y in range(8)},
    }
    print(json.dumps(out,indent=2))

if __name__ == '__main__':
    main()
