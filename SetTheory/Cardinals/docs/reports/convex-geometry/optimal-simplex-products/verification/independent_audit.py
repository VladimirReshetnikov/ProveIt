#!/usr/bin/env python3
"""Independent exact best/runner-up dynamic program for simplex products."""
from fractions import Fraction
from collections import defaultdict
import json

LIMIT = 260
c = [Fraction(1), Fraction(2)]
for d in range(1, LIMIT):
    c.append(c[-1] * Fraction(d + 2, d + 1) * Fraction(d + 1, d) ** d)

gamma = c[14]**8 / (c[13]**4 * c[12]**5)
top = [[(Fraction(1), {()})]]
sharp = []
min_gap = None
for n in range(1, LIMIT + 1):
    vals = defaultdict(set)
    for d in range(1, n + 1):
        for v, ps in top[n-d]:
            val = v*c[d]
            for p in ps:
                vals[val].add(tuple(sorted(p+(d,))))
    keep = sorted(vals, reverse=True)[:2]
    top.append([(v, vals[v]) for v in keep])
    assert len(top[n][0][1]) == 1, (n, top[n][0][1])
    if n >= 100:
        r = n % 13
        expected = ((13,)*((n-14*r)//13)+(14,)*r if r <= 8 else
                    (12,)*(13-r)+(13,)*((n-12*(13-r))//13))
        assert top[n][0][1] == {expected}
        gap = top[n][0][0] / top[n][1][0]
        assert gap >= gamma, (n, float(gap), float(gamma))
        min_gap = gap if min_gap is None else min(min_gap, gap)
        if gap == gamma:
            assert r == 8
            sharp.append(n)

print(json.dumps({
    "dimensions_checked": LIMIT,
    "all_optimizers_unique_as_multisets": True,
    "periodic_formula_verified_from": 100,
    "sharp_gap_decimal": float(gamma),
    "minimum_exact_gap_equals_gamma": min_gap == gamma,
    "dimensions_attaining_gap": sharp,
    "optimizer_dimension_99": sorted(top[99][0][1]),
    "runner_up_dimension_112": sorted(top[112][1][1]),
}, indent=2))
