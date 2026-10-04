#!/usr/bin/env python3
"""Fresh, independent finite probes of the repeated-count recurrence.
No imports or execution of any submitted/upstream code.
"""
from itertools import product
import json

stats = {'recurrence_candidates': 0, 'valid_recurrences': 0, 'selected_legality_cases': 0, 'target_cases': 0}

def pack(ds, b):
    return sum(d * b**i for i, d in enumerate(ds))

# All candidate digits, not merely the intended small cumulative counts.
for b, n, k in [(2, 1, 1), (4, 1, 2), (4, 1, 3), (4, 2, 2), (4, 2, 3), (8, 2, 2)]:
    assert b > k
    q = b**n
    w = q**k
    for interior_bits in product(range(2), repeat=n):
        positions = [j + n*t for t in range(k) for j in range(n) if interior_bits[j]]
        interior = pack(interior_bits, b)
        frame_mask = (b-1)*interior
        event_choices = [sum(e*b**pos for e, pos in zip(es, positions)) for es in product(range(2), repeat=len(positions))]
        for e in event_choices:
            event_digits = [(e // b**i) % b for i in range(n*k)]
            counts = [0]*n
            canonical_a = 0
            for t in range(k):
                canonical_a += pack(counts, b)*q**t
                counts = [counts[j] + event_digits[n*t+j] for j in range(n)]
            canonical_v = pack(counts, b)
            for ads in product(range(b), repeat=len(positions)):
                a = sum(d*b**pos for d, pos in zip(ads, positions))
                numerator = q*(a+e)-a
                stats['recurrence_candidates'] += 1
                if numerator % w:
                    continue
                v = numerator//w
                if v < 0 or (v & frame_mask) != v:
                    continue
                stats['valid_recurrences'] += 1
                assert a == canonical_a
                assert v == canonical_v

# Two selected sites in one frame; a vacant middle slot tests support.
for k, b in [(1, 128), (2, 256), (3, 256), (4, 512)]:
    assert b >= 64*(k+1)
    e = 1 + b**2
    lmask = (b//2 - 1)*e
    cmax = 6*k + 14
    for a0, a1 in product(range(k), repeat=2):
        a = a0 + a1*b**2
        for c0, c1 in product(range(cmax+1), repeat=2):
            c = c0 + c1*b**2
            ell = c - 6*a - 6*e
            accepts = ell >= 0 and (ell & lmask) == ell
            direct = c0 >= 6*a0+6 and c1 >= 6*a1+6
            stats['selected_legality_cases'] += 1
            assert accepts == direct

for b, n, k in [(128, 1, 1), (256, 2, 2), (256, 3, 3)]:
    q = b**n
    for es in product(range(2), repeat=n*k):
        e = pack(es, b)
        for j in range(n):
            for tau in range(k+2):
                point = b**j*q**tau
                accepts = (e & point) == point
                direct = tau < k and bool(es[n*tau+j])
                stats['target_cases'] += 1
                assert accepts == direct

# Demonstrate why a radix large enough for counts matters.
b, n, k = 2, 2, 2
q = b**n
a, e, v = q, 1+q, b
assert q*(a+e) == a+q**k*v
assert [(v // b**j) % b for j in range(n)] == [0, 1]
assert [sum((e // b**(j+n*t)) % b for t in range(k)) for j in range(n)] == [2, 0]
stats["undersized_radix_counterexample"] = {"b": b, "N": n, "K": k, "Apre": a, "E": e, "V": v}
print(json.dumps(stats, indent=2, sort_keys=True))
