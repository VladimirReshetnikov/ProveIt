#!/usr/bin/env python3
"""Remove the two linearly defined positive coordinates from the 49-DAG."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
parent = D.parent / 'adaptive-square-sums49/candidate.json'
raw = parent.read_bytes()
if hashlib.sha256(raw).hexdigest() != 'f3056e44b4833f75becb663e939f28c09a883d96cbdbd301c7e1cde5f3336984':
    raise ValueError('parent pin')
p = json.loads(raw)
w = p['witnesses']
if w[17:19] != ['cVariable', 'aVariable']:
    raise ValueError('unexpected coordinates')
w = w[:17] + w[19:]
removed = {'cDifference', 'cConstraint', 'aDifference', 'aConstraint', 'addC', 'addA'}
table = {r[0]: r for r in p['source']}
expected = {
    'c': ['c', '+', 'eta', 'ySumVariable'],
    'a': ['a', '+', 'productVariable2', 'Y'],
    'cDifference': ['cDifference', '-', 'cVariable', 'c'],
    'cConstraint': ['cConstraint', '*', 'cDifference', 'cDifference'],
    'aDifference': ['aDifference', '-', 'aVariable', 'a'],
    'aConstraint': ['aConstraint', '*', 'aDifference', 'aDifference'],
    'addC': ['addC', '+', 'finalWithRank', 'cConstraint'],
    'addA': ['addA', '+', 'addC', 'aConstraint'],
    'addEll': ['addEll', '+', 'addA', 'ellConstraint'],
}
if any(table.get(k) != v for k, v in expected.items()):
    raise ValueError('parent binding differs')
rows = []
for name, op, left, right in p['source']:
    if name in removed:
        continue
    left = {'cVariable': 'c', 'aVariable': 'a', 'addA': 'finalWithRank'}.get(left, left)
    right = {'cVariable': 'c', 'aVariable': 'a', 'addA': 'finalWithRank'}.get(right, right)
    rows.append([name, op, left, right])
table = {r[0]: r for r in rows}
known = set(w + p['fixed_numerals'])
live = {p['output']}
todo = list(live)
for name, op, left, right in rows:
    if name in known or any(isinstance(x, str) and x not in known for x in (left, right)):
        raise ValueError(('invalid topological row', name))
    known.add(name)
while todo:
    name = todo.pop()
    if name in table:
        for x in table[name][2:]:
            if isinstance(x, str) and x not in live:
                live.add(x)
                todo.append(x)
if not set(table) <= live or not set(w + p['fixed_numerals']) <= live:
    raise ValueError('dead node or input')
if len(w) != 47 or len(rows) != 179:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; model zero equivalence and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 47 variables, 179 live circuit rows; model equivalence is not yet checked')
