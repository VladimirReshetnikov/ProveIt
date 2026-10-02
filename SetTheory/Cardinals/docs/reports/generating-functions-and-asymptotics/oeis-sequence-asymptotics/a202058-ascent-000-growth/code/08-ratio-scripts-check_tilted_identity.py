#!/usr/bin/env python3
"""Finite exact coefficient checks of the tilted identities, not limit proofs."""
from collections import defaultdict
import json

def children(x):
    s, u, k = x
    for i in range(s + u):
        yield (s - 1, u + int(i >= k), i) if i < s else (s + 1, u - int(i < k), i + 1)

starts = [(0, 1, 0), (7, 1, 7), (4, 2, 4)]
max_degree = 14
checks = 0
for x in starts:
    states = {x: 1}
    b, m1, m2, drift = [], [], [], []
    for j in range(max_degree + 1):
        b.append(sum(states.values()))
        m1.append(sum(v * (s + u) for (s, u, k), v in states.items()))
        m2.append(sum(v * (s + u)**2 for (s, u, k), v in states.items()))
        drift.append(sum(v * (u - k) for (s, u, k), v in states.items()))
        nxt = defaultdict(int)
        for state, multiplicity in states.items():
            for child in children(state):
                nxt[child] += multiplicity
        states = nxt
    for r in range(max_degree + 1):
        # Coefficients use the exponential basis t^r/r!.
        lhs = r*r*b[r]
        rhs = r*b[r]
        if r >= 1:
            lhs -= 2*r*(r-1)*m1[r-1]
            assert r*b[r] - r*m1[r-1] == 0
        if r >= 2:
            lhs += r*(r-1)*m2[r-2]
            rhs -= r*(r-1)*drift[r-2]
            assert b[r] == m2[r-2] + drift[r-2]
        # Signed coefficients need not be positive; only equality is checked.
        assert lhs == rhs, (x, r)
        checks += 1
print(json.dumps({"passed": True, "starting_states": starts,
                  "max_series_degree": max_degree,
                  "exact_square_identity_coefficients": checks}, sort_keys=True))
