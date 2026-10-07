#!/usr/bin/env python3
"""Reproducible exact checks for the accompanying research manuscript."""
from __future__ import annotations
import csv
import json
import random
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from anchor_selection import (Row, choose, class_loss, low_occupancy_identity,
    universal_bound, minimax_profile, conditional_mass, select_anchors,
    discarded_mass, exact_average)

ROOT = Path(__file__).resolve().parents[1]
RNG = random.Random(20261006)
checks: dict[str, int] = {}

# 1. Two formulas against direct subset enumeration, including all edge cases.
count = 0
for m in range(1, 11):
    for r in range(m+1):
        subsets = [frozenset(a) for a in combinations(range(m), r)]
        for t in range(1, 5):
            for s in range(m+1):
                cls = frozenset(range(s))
                brute = Fraction(sum(len(cls-a) if len(cls & a) < t else 0
                                     for a in subsets), m*len(subsets))
                exact = class_loss(m, r, t, s)
                assert exact == brute == low_occupancy_identity(m, r, t, s)
                assert exact <= universal_bound(m, r, t, 1)
                count += 1
checks['exact_marginal_and_double_counting_cases'] = count

# 2. DP profile optimization against every ordered size profile for small m.
count = 0
for m in range(1, 8):
    for q in range(1, 4):
        for r in range(m+1):
            for t in range(1, 4):
                value, sizes = minimax_profile(m, q, r, t)
                brute = max(sum((class_loss(m, r, t, s) for s in ss), Fraction(0))
                            for ss in product(range(m+1), repeat=q) if sum(ss) <= m)
                assert value == brute
                assert len(sizes) == q and sum(sizes) <= m
                assert value == sum((class_loss(m, r, t, s) for s in sizes), Fraction(0))
                assert value <= universal_bound(m, r, t, q)
                count += 1
checks['exact_dynamic_program_cases'] = count

# 3. Exact minimax lower certificate: all assignments with a fixed profile.
# Enumerating assignments realizes the permutation orbit with equal weights.
orbits = []
count = 0
for m, q, r, t in [(6, 2, 2, 2), (7, 2, 3, 2), (7, 2, 4, 3), (6, 2, 3, 1)]:
    value, sizes = minimax_profile(m, q, r, t)
    rows = []
    for assignment in product(range(q+1), repeat=m):
        if all(assignment.count(i) == sizes[i] for i in range(q)):
            rows.append(Row.make([[x for x in range(m) if assignment[x] == i]
                                  for i in range(q)]))
    values = [discarded_mass(m, rows, a, t) for a in combinations(range(m), r)]
    assert all(v == value for v in values)
    orbits.append(dict(m=m, q=q, r=r, threshold=t, profile=sizes,
                       rows=len(rows), anchor_sets=len(values), exact_value=str(value)))
    count += len(values)
checks['permutation_orbit_anchor_sets'] = count

# 4. Weighted derandomization and conditional-expectation identities.
count = 0
examples = []
for trial in range(80):
    m = RNG.randrange(2, 10)
    q = RNG.randrange(1, 4)
    r = RNG.randrange(m+1)
    t = RNG.randrange(1, 5)
    rows = []
    for _ in range(RNG.randrange(1, 6)):
        labels = [RNG.randrange(q+1) for _ in range(m)]
        rows.append(Row.make([[x for x, label in enumerate(labels) if label == j]
                              for j in range(q)], Fraction(RNG.randrange(1, 5), RNG.randrange(1, 4))))
    anchors, trace = select_anchors(m, rows, r, t)
    expected = exact_average(m, rows, r, t)
    assert trace[0] == expected
    assert trace[-1] <= expected <= universal_bound(m, r, t, q)
    current = frozenset()
    for x in anchors:
        if len(current) == r:
            break
        child_potentials = [conditional_mass(m, rows, current | {y}, r, t)
                            for y in range(m) if y not in current]
        assert sum(child_potentials, Fraction(0))/len(child_potentials) == conditional_mass(m, rows, current, r, t)
        current |= {x}
        count += 1
    if trial < 5:
        examples.append(dict(m=m, q=q, r=r, threshold=t, anchors=anchors,
                             potential_trace=[str(z) for z in trace]))
checks['weighted_derandomization_instances'] = 80
checks['conditional_expectation_identities'] = count

# 5. Lagrange recovery and noisy-row witness over finite prime fields.
def evaluate(coefficients, x, p):
    return sum(c*pow(x, j, p) for j, c in enumerate(coefficients)) % p

def lagrange(points, values, x, p):
    result = 0
    for i, a in enumerate(points):
        num = den = 1
        for j, b in enumerate(points):
            if i != j:
                num = num*(x-b) % p
                den = den*(a-b) % p
        result = (result + values[i]*num*pow(den, -1, p)) % p
    return result

count = 0
for p in [5, 7, 11]:
    for t in [1, 2, 3, 4]:
        for trial in range(15):
            m = p
            q = 2
            labels = [RNG.randrange(q+1) for _ in range(m)]
            classes = [frozenset(x for x in range(m) if labels[x] == j) for j in range(q)]
            coeffs = [[RNG.randrange(p) for _ in range(t)] for _ in range(q)]
            values = {x: evaluate(coeffs[j], x, p) for j in range(q) for x in classes[j]}
            r = min(m, t+1)
            anchors, _ = select_anchors(m, [Row.make(classes)], r, t)
            A = frozenset(anchors)
            for j, cls in enumerate(classes):
                hits = sorted(cls & A)
                for x in cls:
                    if x in A:
                        continue  # A sampled target is covered by its actual horizontal section.
                    elif len(hits) >= t:
                        nodes = hits[:t]
                        assert lagrange(nodes, [values[a] for a in nodes], x, p) == values[x]
                        count += 1
checks['finite_field_interpolation_recoveries'] = count

# 6. Label-preserving candidate cardinalities (formal symbolic index counts).
count = 0
for r in range(0, 9):
    for L in range(1, 6):
        for t in range(1, 5):
            counted = r*L + sum(L**t for _ in combinations(range(r), t))
            assert counted == r*L + choose(r, t)*L**t
            count += 1
checks['candidate_cardinality_cases'] = count

(ROOT/'data').mkdir(exist_ok=True)
with (ROOT/'data'/'exact_profiles.csv').open('w', newline='') as out:
    writer = csv.writer(out)
    writer.writerow(['m','q','r','threshold','exact_minimax','decimal_minimax','maximizing_profile','universal_bound'])
    for m, q, t in [(20, 2, 2), (40, 3, 2), (40, 3, 3)]:
        for r in [1, 2, 4, 8, 12, 16]:
            if r <= m:
                v, ss = minimax_profile(m, q, r, t)
                writer.writerow([m,q,r,t,str(v),float(v),' '.join(map(str,ss)),str(universal_bound(m,r,t,q))])

result = {'status':'all checks passed', 'seed':20261006,
          'arithmetic':'exact Python integers and fractions.Fraction',
          'checks':checks, 'total_checked_cases':sum(checks.values()),
          'minimax_orbit_certificates':orbits, 'sample_derandomization_traces':examples,
          'scope':'Finite tests support, but do not replace, the manuscript proofs. No Lean verification was performed.'}
(ROOT/'certificates').mkdir(exist_ok=True)
(ROOT/'certificates'/'verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
