#!/usr/bin/env python3
"""Read-only cross-check of sibling code against this audit's independent model."""
import importlib.util
from pathlib import Path
from random import Random
from independent_audit import PATS, trans, neighborhood, component_step, formula_count, formula_visited, T, stage
from independent_drift_audit import C, arrival
ROOT = Path(__file__).resolve().parent.parent

def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'code' / f'{name}.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m
c, l, e = map(module, ['component_rule', 'local_rule', 'exact_formulas'])
cases = [set()]
for P, Q in PATS.values():
    for a in [(0, 0), (-20, 6), (17, -29)]:
        S = trans(P, a)
        cases.append(S)
        cases.extend((S | {p} for p in neighborhood(S) - S))
rng = Random(10703)
for _ in range(400):
    cases.append({(rng.randrange(-14, 15), rng.randrange(-10, 11)) for _ in range(rng.randrange(55))})
for S in cases:
    expected = component_step(S)
    if not c.step(S) == expected:
        raise RuntimeError('Audit check failed: c.step(S) == expected')
    if not l.step(S) == expected:
        raise RuntimeError('Audit check failed: l.step(S) == expected')
    if not l.drift_step(S) == {(x, y + 1) for x, y in expected}:
        raise RuntimeError('Audit check failed: l.drift_step(S) == {(x, y + 1) for x, y in expected}')
for k in range(7, 51):
    for n in range(25):
        d = k + n
        for j in range(2 * d - 10):
            expected = stage(k, n, j, 'E') if j <= d - 6 else stage(k, n, j - (d - 5), 'W')
            if not c.phase_support(k, n, j) == expected:
                raise RuntimeError('Audit check failed: c.phase_support(k, n, j) == expected')
        for x, y in formula_visited(k, n):
            if not e.visited(k, x, y):
                raise RuntimeError('Audit check failed: e.visited(k, x, y)')
            if not e.first_arrival(k, x, y) == arrival(k, n, x):
                raise RuntimeError('Audit check failed: e.first_arrival(k, x, y) == arrival(k, n, x)')
        if not not e.visited(k, 1, n):
            raise RuntimeError('Audit check failed: not e.visited(k, 1, n)')
        if not not e.visited(k, k + n - 1, n):
            raise RuntimeError('Audit check failed: not e.visited(k, k + n - 1, n)')
    for N in range(501):
        if not e.centered_count(k, N) == formula_count(k, N):
            raise RuntimeError('Audit check failed: e.centered_count(k, N) == formula_count(k, N)')
        if N >= k + 1:
            if not e.drift_count(k, N) == C(k, N):
                raise RuntimeError('Audit check failed: e.drift_count(k, N) == C(k, N)')
print(f'PASS: parent component/local implementation on {len(cases)} independent cases, including every single-site halo interference; exact phase/arrival formulas for 44 k values × 25 rounds; counts through radius 500.')
