#!/usr/bin/env python3
"""Standalone exact certificate; no optional dependency is needed."""
from math import comb

def check(condition):
    if not condition:
        raise RuntimeError("Certificate check failed")

digits = [[(9, 1)], [(7, 2), (5, 1)], [(6, 3), (3, 2), (1, 1)]]
f, g, h = [1], [1], []
for expansion in digits:
    f.append(sum(comb(a, k) for a, k in expansion))
    g.append(sum(comb(a-1, k) if a-1 >= k else 0 for a, k in expansion))
    h.append(sum(comb(a-1, k-1) for a, k in expansion))
check(f == [1, 9, 26, 24])
check(g == [1, 8, 19, 11] and h == [1, 7, 13])
check(all(f[k] == g[k] + h[k-1] for k in range(1, 4)))
check(7**2 - 4*13 == -3)
check(19**2*8**2 - 4*11*8**3 - 4*19**3 - 27*11**2 + 18*11*19*8 == -31)
print("Exact counterexample verified")
