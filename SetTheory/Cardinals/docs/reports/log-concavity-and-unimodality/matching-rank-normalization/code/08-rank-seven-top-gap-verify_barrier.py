#!/usr/bin/env python3
from itertools import combinations
from random import Random
from fractions import Fraction as Q
from pathlib import Path
import json, sys
sys.path.insert(0, str(Path(__file__).parent))
from endpoint_profiles import coefficient_profiles, endpoints
rng = Random(457827)
p = 1009

def rref(rows, b):
    A = [list(x) for x in rows]
    piv = []
    r = 0
    for c in range(b):
        hit = next((i for i in range(r, len(A)) if A[i][c] % p), None)
        if hit is None:
            continue
        A[r], A[hit] = (A[hit], A[r])
        z = pow(A[r][c] % p, -1, p)
        A[r] = [x * z % p for x in A[r]]
        for i in range(len(A)):
            if i != r:
                z = A[i][c]
                A[i] = [(v - z * w) % p for v, w in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    return (A[:r], piv)

def rank(rows, b):
    return len(rref(rows, b)[1])
planes = 0
for b in [3, 4, 5, 6]:
    for case in range(80):
        n = b + rng.randrange(5)
        rows = [[int(i == j) for j in range(b)] for i in range(b)]
        rows += [[rng.randrange(3) if rng.random() < 0.65 else 0 for j in range(b)] for _ in range(n - b)]
        rows = [x for x in rows if any(x)]
        H = [[int(i == j) for j in range(b)] for i in range(2)]
        beta = sum((rank([*H, *[rows[i] for i in J]], b) == b for J in combinations(range(len(rows)), b - 2)))
        q = sum((rank([rows[i] for i in J], b) == b for J in combinations(range(len(rows)), b)))
        classes = {}
        for J in combinations(range(len(rows)), b - 1):
            A, piv = rref([rows[i] for i in J], b)
            if len(piv) != b - 1:
                continue
            free = next((i for i in range(b) if i not in piv))
            v = [0] * b
            v[free] = 1
            for i, c in enumerate(piv):
                v[c] = -A[i][free] % p
            w = v[:2]
            if not any(w):
                continue
            z = pow(next((x for x in w if x)), -1, p)
            key = tuple((x * z % p for x in w))
            classes[key] = classes.get(key, 0) + 1
        h = sum(classes.values())
        ordered = h * h - sum((x * x for x in classes.values()))
        if not (b - 1) * ordered >= b * q * beta:
            raise RuntimeError('Exact verification failed')
        if not (b * (b - 1) * q >= 2 * beta and (b - 1) * h >= 2 * beta):
            raise RuntimeError('Exact verification failed')
        planes += 1
profiles = 0
top = 0
for a, b in [(3, 3), (3, 4), (3, 5), (4, 3), (2, 5)]:
    for case in range(20):
        core = [rng.randrange(1 << b) for _ in range(a)]
        left = [1 << i for i in range(b)] + [rng.randrange(1, 1 << b) for _ in range(2)]
        right = [1 << i for i in range(a)] + [rng.randrange(1, 1 << a) for _ in range(2)]
        weights = [rng.randrange(1, 5) for _ in right]
        basecols = [sum((1 << i for i, row in enumerate(core + left) if row >> j & 1)) for j in range(b)]
        C = []
        for j in range(a + 1):
            s = 0
            for I in combinations(range(len(right)), j):
                w = 1
                for i in I:
                    w *= weights[i]
                s += w * len(endpoints(tuple(sorted(basecols + [right[i] for i in I]))))
            C.append(s)
        prof = coefficient_profiles(core, left, a, b)
        elem = {t: [1] + [0] * a for t in range(1, 1 << a)}
        for t, w in zip(right, weights):
            for j in range(a, 0, -1):
                elem[t][j] += w * elem[t][j - 1]
        for j, entries in enumerate(prof):
            v = 0
            for R, c in entries:
                for t in set(R):
                    c *= elem[t][R.count(t)]
                v += c
            if not v == C[j]:
                raise RuntimeError((a, b, case, j, v, C[j]))
            profiles += 1
        if not (a - 1) * (b * b + b + 2) * C[a - 1] ** 2 >= a * (b + 2) ** 2 * C[a - 2] * C[a]:
            raise RuntimeError('Exact verification failed')
        top += 1
out = dict(scope='Exact finite-field incidence and endpoint-set regressions; the universal theorem is proved separately', plane_configurations=planes, endpoint_profile_coefficient_checks=profiles, top_gap_checks=top, all_pass=True)
(Path(__file__).resolve().parents[1] / 'data' / 'barrier_checks.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
