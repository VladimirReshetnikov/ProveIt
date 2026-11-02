#!/usr/bin/env python3
"""Check standard examples of the marker indexing, including N=1; no Lean."""
import json
P = 8807
count = 0
for N in range(1, 21):
    for h in range(N):
        g = (h + 1) % N
        k = P*g + 1073
        assert (k-62) % (P*N) == P*g+1011
        assert (k-8849) % (P*N) == P*h+1031
        assert (g-1) % N == h
        count += 1
print(json.dumps({'checked_N': [1, 20], 'cases': count,
                  'N1_current_marker': (1073-62) % P,
                  'N1_previous_marker': (1073-8849) % P,
                  'N1_successor': (0+1) % 1, 'lean_launched': False},
                 indent=2, sort_keys=True))
