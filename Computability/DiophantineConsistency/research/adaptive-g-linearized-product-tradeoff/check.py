#!/usr/bin/env python3
"""Check the exact G rewrite and its effect on the two 13-variable DAGs."""
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
     {'*': 48, '+': 21, '-': 18}, {'*': 47, '+': 20, '-': 20}),
    ('adaptive-direct-ordinate86/candidate.json', 'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f',
     {'*': 47, '+': 21, '-': 18}, {'*': 46, '+': 20, '-': 20}),
)

# Independent sparse-polynomial calculation in Z[b,F,alpha].
zero = (0, 0, 0)
one, b, F, alpha = {zero: 1}, {(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1}
def add(a, c, sign=1):
    out = dict(a)
    for m, n in c.items(): out[m] = out.get(m, 0) + sign*n
    return {m: n for m, n in out.items() if n}
def mul(a, c):
    out = {}
    for x, m in a.items():
        for y, n in c.items():
            key = tuple(i+j for i, j in zip(x, y))
            out[key] = out.get(key, 0) + m*n
    return {m: n for m, n in out.items() if n}
q = add(one, b)
qF = add(q, F, -1)
C = add(qF, alpha, -1)
old = add(alpha, mul(qF, b))
new = add(add(mul(q, q), mul(F, q), -1), C, -1)
wrong = add(add(mul(q, q), mul(F, q), -1), C)
assert old == new and old != wrong

def validate(rows, graph):
    inputs = set(graph['witnesses'] + graph['fixed_numerals'])
    scope = set(inputs)
    assert len(graph['witnesses']) == 13 and len(graph['fixed_numerals']) == 4
    for name, op, left, right in rows:
        assert name not in scope and op in ('+', '-', '*')
        for value in (left, right):
            assert isinstance(value, int) or value in scope
        scope.add(name)
    index = {row[0]: row for row in rows}
    assert len(index) == len(rows)
    seen, todo = set(), [graph['output']]
    while todo:
        name = todo.pop()
        if name in seen: continue
        seen.add(name)
        if name in index: todo.extend(x for x in index[name][2:] if isinstance(x, str))
    assert set(index) <= seen and inputs <= seen
    return inputs

ops = {'+': operator.add, '-': operator.sub, '*': operator.mul}
def evaluate(rows, output, values):
    values = dict(values)
    def value(x): return x if isinstance(x, int) else values[x]
    for name, op, left, right in rows: values[name] = ops[op](value(left), value(right))
    return values[output]

results = []
for rel, pin, old_counts, new_counts in INPUTS:
    path = HERE.parent / rel
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == pin
    graph = json.loads(raw)
    rows = graph['source']
    by_name = {row[0]: row for row in rows}
    for row in (['q', '+', 1, 'qm'], ['q2', '*', 'q', 'q'],
                ['qF', '-', 'q', 'F'], ['C', '-', 'qF', 'alpha'],
                ['g28', '*', 'F', 'q'], ['g44', '*', 'qF', 'qm'],
                ['G', '+', 'alpha', 'g44']):
        assert by_name[row[0]] == row
    assert [row[0] for row in rows if 'g44' in row[2:]] == ['G']
    changed = [row[:] for row in rows]
    pos = next(i for i, row in enumerate(changed) if row[0] == 'g44')
    assert changed[pos+1][0] == 'G'
    changed[pos:pos+2] = [['g44', '-', 'q2', 'g28'], ['G', '-', 'g44', 'C']]
    inputs = validate(rows, graph)
    assert validate(changed, graph) == inputs
    assert dict(Counter(row[1] for row in rows)) == old_counts
    assert dict(Counter(row[1] for row in changed)) == new_counts
    assert len(rows) == len(changed)
    rng = random.Random(8405)
    for _ in range(50):
        values = {name: rng.randrange(-3, 4) for name in sorted(inputs)}
        assert evaluate(rows, graph['output'], values) == evaluate(changed, graph['output'], values)
    results.append({'input': rel, 'sha256': pin, 'operations': len(rows),
                    'old_counts': old_counts, 'new_counts': new_counts,
                    'witnesses': 13, 'ports': 4, 'samples': 50})
print('PASS_EXACT_G_REWRITE', json.dumps(results, sort_keys=True))
