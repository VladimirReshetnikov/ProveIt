#!/usr/bin/env python3
"""Substitute positive a and Q coordinates into the degree-six parent DAG."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums42/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != 'be55ec0103d0114973b44dfdf1dff5b5fe3a9fd24cf88dd6bf8badcaf180cac0':
    raise ValueError('parent pin')
p = json.loads(raw)
w = p['witnesses']
if w[18] != 'aVariable' or w[-2:] != ['qPositive', 'qNegative']:
    raise ValueError('unexpected coordinates')
w = w[:18] + w[19:-2] + ['qValueVariable']
table = {r[0]: r for r in p['source']}
expected = {
    'a': ['a', '+', 'productVariable2', 'Y'],
    'aDifference': ['aDifference', '-', 'aVariable', 'a'],
    'aConstraint': ['aConstraint', '*', 'aDifference', 'aDifference'],
    'addA': ['addA', '+', 'addC', 'aConstraint'],
    'addEll': ['addEll', '+', 'addA', 'ellConstraint'],
    'Q': ['Q', '-', 'qPositive', 'qNegative'],
    'g72': ['g72', '-', 'g71', 'Q'],
}
if any(table.get(k) != v for k, v in expected.items()):
    raise ValueError('parent binding differs')
rows = []
for name, op, left, right in p['source']:
    if name in {'aDifference', 'aConstraint', 'addA', 'Q'}:
        continue
    changes = {'aVariable': 'a', 'addA': 'addC', 'Q': 'qValueVariable'}
    left, right = changes.get(left, left), changes.get(right, right)
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
if len(w) != 40 or len(rows) != 160:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; model zero equivalence and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 40 variables, 160 live circuit rows; model equivalence remains open')
