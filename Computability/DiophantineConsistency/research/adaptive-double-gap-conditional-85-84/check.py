#!/usr/bin/env python3
"""Check a conditional two-gap DAG rewrite; not an unrestricted equation."""
from collections import Counter
import hashlib
import json
import operator
from pathlib import Path
import random

if not __debug__:
    raise RuntimeError('this check requires Python assertions enabled')
HERE = Path(__file__).resolve().parent
INPUTS = (
    ('adaptive-square-sums/candidate.json', '11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828',
     87, 85, {'*': 47, '+': 20, '-': 18}),
    ('adaptive-direct-ordinate86/candidate.json', 'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f',
     86, 84, {'*': 46, '+': 20, '-': 18}),
)

# Exact sparse identities in the free polynomial ring Z[q,H,C].
zero = (0, 0, 0)
one, q, H, C = {zero: 1}, {(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1}
def add(a, b, sign=1):
    out = dict(a)
    for m, n in b.items(): out[m] = out.get(m, 0) + sign*n
    return {m: n for m, n in out.items() if n}
def mul(a, b):
    out = {}
    for x, m in a.items():
        for y, n in b.items():
            key = tuple(i+j for i, j in zip(x, y))
            out[key] = out.get(key, 0) + m*n
    return {m: n for m, n in out.items() if n}
old_F = add(q, H, -1)
old_alpha = add(H, C, -1)
old_Fq = mul(old_F, q)
new_Fq = add(mul(q, q), mul(q, H), -1)
old_G = add(old_alpha, mul(H, add(q, one, -1)))
new_G = add(mul(q, H), C, -1)
assert old_Fq == new_Fq and old_G == new_G
assert old_Fq != add(mul(q, q), mul(q, H))  # altered sign
assert old_G != add(mul(q, H), C)             # altered sign

def validate(rows, output, inputs):
    scope = set(inputs)
    for name, op, left, right in rows:
        assert name not in scope and op in ('+', '-', '*')
        for value in (left, right): assert isinstance(value, int) or value in scope
        scope.add(name)
    index = {row[0]: row for row in rows}
    assert len(index) == len(rows)
    seen, todo = set(), [output]
    while todo:
        name = todo.pop()
        if name in seen: continue
        seen.add(name)
        if name in index: todo.extend(x for x in index[name][2:] if isinstance(x, str))
    assert set(index) <= seen and set(inputs) <= seen

ops = {'+': operator.add, '-': operator.sub, '*': operator.mul}
def evaluate(rows, output, values):
    values = dict(values)
    def value(x): return x if isinstance(x, int) else values[x]
    for name, op, left, right in rows: values[name] = ops[op](value(left), value(right))
    return values[output]

results = []
for rel, pin, old_count, new_count, counts in INPUTS:
    raw = (HERE.parent / rel).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == pin
    graph = json.loads(raw)
    original = graph['source']
    by_name = {row[0]: row for row in original}
    required = (['q', '+', 1, 'qm'], ['q2', '*', 'q', 'q'],
                ['qF', '-', 'q', 'F'], ['C', '-', 'qF', 'alpha'],
                ['g28', '*', 'F', 'q'], ['g44', '*', 'qF', 'qm'],
                ['G', '+', 'alpha', 'g44'])
    assert all(by_name[row[0]] == row for row in required)
    assert {row[0] for row in original if 'F' in row[2:]} == {'qF', 'g28'}
    assert {row[0] for row in original if 'alpha' in row[2:]} == {'C', 'G'}
    changed = []
    for row in original:
        name = row[0]
        if name in ('qF', 'C', 'g44'): continue
        if name == 'g28': changed.extend([['g44', '*', 'q', 'qF'], ['g28', '-', 'q2', 'g44']])
        elif name == 'G': changed.append(['G', '-', 'g44', 'C'])
        else: changed.append(row[:])
    witnesses = [('qF' if n == 'F' else 'C' if n == 'alpha' else n) for n in graph['witnesses']]
    assert len(witnesses) == len(set(witnesses)) == 13 and len(graph['fixed_numerals']) == 4
    old_inputs = graph['witnesses'] + graph['fixed_numerals']
    new_inputs = witnesses + graph['fixed_numerals']
    validate(original, graph['output'], old_inputs)
    validate(changed, graph['output'], new_inputs)
    assert len(original) == old_count and len(changed) == new_count
    assert dict(Counter(row[1] for row in changed)) == counts
    rng = random.Random(8425)
    for _ in range(50):
        env = {name: rng.randrange(-3, 4) for name in sorted(new_inputs)}
        current_q = 1 + env['J'] * env['beta']
        old = dict(env, F=current_q-env['qF'], alpha=env['qF']-env['C'])
        assert evaluate(original, graph['output'], old) == evaluate(changed, graph['output'], env)
    results.append({'input': rel, 'sha256': pin, 'old_operations': old_count,
                    'new_operations': new_count, 'new_counts': counts,
                    'witnesses': 13, 'ports': 4, 'samples': 50})

# Positive new inputs alone do not enforce either reverse inequality. These
# are domain examples only; they are not asserted to be polynomial zeros.
assert 1 + 1*1 == 2
assert 3 > 1 > 0 and 2-3 < 0 and 3-1 > 0  # q=2, H=3, C=1
assert 2 > 1 > 0 and 2-1 > 0 and 1-2 < 0  # q=2, H=1, C=2
print('PASS_CONDITIONAL_DOUBLE_GAP', json.dumps(results, sort_keys=True))
