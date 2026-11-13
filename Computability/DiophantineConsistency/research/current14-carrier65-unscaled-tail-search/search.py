#!/usr/bin/env python3
"""Exact quotient identity and bounded joint monomial-circuit enumeration."""
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
SOURCE = D / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
QUOTIENT = D / 'research/current2011-unscaled66/polynomial.json'
pins = {SOURCE: 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e',
        QUOTIENT: 'bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75'}
for file, digest in pins.items():
    if hashlib.sha256(file.read_bytes()).hexdigest() != digest:
        raise RuntimeError(f'source hash mismatch: {file}')
parent, quotient = [json.loads(p.read_bytes()) for p in (SOURCE, QUOTIENT)]

def live(rows, output):
    deps = {n: (a, b) for n, _, a, b in rows}
    seen, pending = set(), [output]
    while pending:
        n = pending.pop()
        if n in deps and n not in seen:
            seen.add(n)
            pending.extend(deps[n])
    return seen

for graph, expected in ((parent, 65), (quotient, 66)):
    if len(graph['source']) != expected or len(live(graph['source'], graph['output'])) != expected:
        raise RuntimeError('unexpected graph size/liveness')
if parent['source'][:51] != quotient['source'][:51]:
    raise RuntimeError('unexpected common prefix')

# Sparse exact polynomial ring in A, Delta, i, c2, f2, V, y.
N = 7
zero = (0,) * N
def var(i):
    x = list(zero); x[i] = 1
    return {tuple(x): 1}
def add(a, b):
    r = Counter(a); r.update(b)
    return {k: v for k, v in r.items() if v}
def neg(a): return {k: -v for k, v in a.items()}
def sub(a, b): return add(a, neg(b))
def mul(a, b):
    r = Counter()
    for x, cx in a.items():
        for y, cy in b.items():
            r[tuple(a + b for a, b in zip(x, y))] += cx * cy
    return {k: v for k, v in r.items() if v}
one = {zero: 1}
A, delta, i, c2, f2, v, y = [var(j) for j in range(N)]
v2, y2 = mul(v, v), mul(y, y)
s = mul(i, mul(delta, c2)); s2 = mul(s, s)
strong = mul(delta, mul(mul(i, i), mul(c2, c2)))
old_u = add(mul(s2, sub(v2, y2)), y2)
old_z = sub(mul(delta, f2), s2)
old = sub(mul(mul(A, old_u), old_z), delta)
new_u = add(mul(mul(delta, strong), sub(v2, y2)), y2)
new_z = sub(f2, strong)
new = sub(mul(mul(A, new_u), new_z), one)
if old != mul(delta, new):
    raise RuntimeError('exact quotient identity failed')
def evaluate_tail(graph):
    env = {'N0': A, 'N1': one, 'Nt': one, 'Delta': delta, 'i': i, 'c2': c2,
           'Dc2': mul(delta, c2), 'f2': f2, 'V': v, 'y': y, 1: one}
    operations = {'+': add, '-': sub, '*': mul}
    for name, op, left, right in graph['source'][51:]:
        env[name] = operations[op](env[left], env[right])
    return env[graph['output']]
if evaluate_tail(parent) != old or evaluate_tail(quotient) != new:
    raise RuntimeError('graph suffix does not match checked identity')

# A monomial is an exponent vector (delta, i, c2).  Existing leaves are
# delta, i, c2 and the shared delta*c2 already required by the main norm.
atoms = frozenset(((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1)))
@lru_cache(None)
def circuits(target):
    choices = set()
    if target in atoms:
        choices.add(frozenset())
    for a0 in range(target[0] + 1):
      for a1 in range(target[1] + 1):
       for a2 in range(target[2] + 1):
        a = (a0, a1, a2); b = tuple(x-y for x, y in zip(target, a))
        if a == zero3 or b == zero3 or a > b:
            continue
        for left in circuits(a):
         for right in circuits(b):
          choices.add(left | right | frozenset((target,)))
    # A strict superset cannot improve any union with a second circuit.
    return tuple(x for x in choices if not any(y < x for y in choices))
zero3 = (0, 0, 0)
t, dt = (1, 2, 2), (2, 2, 2)
first, second = circuits(t), circuits(dt)
unions = {a | b for a in first for b in second}
minimum = min(map(len, unions))
if minimum != 4:
    raise RuntimeError('unexpected joint monomial minimum')
witness = sorted(sorted(x) for x in unions if len(x) == minimum)[0]
counts = {'old': dict(Counter(row[1] for row in parent['source'])),
          'quotient': dict(Counter(row[1] for row in quotient['source']))}
result = {'parent_sha256': pins[SOURCE], 'quotient_sha256': pins[QUOTIENT],
          'wrapper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'exact_identity': 'old = Delta * quotient', 'old_terms': len(old),
          'quotient_terms': len(new), 'prefix_rows_equal': 51,
          'operation_counts': counts, 'available_monomial_atoms': sorted(atoms),
          'strong_monomial': list(t), 'auxiliary_monomial': list(dt),
          'strong_minimal_circuits': len(first), 'aux_minimal_circuits': len(second),
          'candidate_unions': len(unions), 'minimum_new_multiplications': minimum,
          'minimum_witness_exponent_vectors': witness}
print(json.dumps(result, sort_keys=True, indent=2))
