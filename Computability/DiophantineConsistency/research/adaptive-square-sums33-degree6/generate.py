#!/usr/bin/env python3
"""Replace the signed W pair with a single positive coordinate."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums34/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != '9c7fdcf0289b0407af4bbb9deaef4d52fd37435c162a8d15199d1ec9902e1f77':
    raise ValueError('parent pin')
p = json.loads(raw)
w = p['witnesses']
if w[18:20] != ['wPositive', 'wNegative']:
    raise ValueError('unexpected W coordinates')
w = w[:18] + ['wValueVariable'] + w[20:]
table = {r[0]: r for r in p['source']}
expected = {'namedBt': ['namedBt', '-', 'wPositive', 'wNegative'],
            'root_skew': ['root_skew', '*', 'k', 'namedBt'],
            'wDifference': ['wDifference', '-', 'namedBt', 'Bt']}
if any(table.get(k) != v for k, v in expected.items()):
    raise ValueError('parent binding differs')
rows = []
for name, op, left, right in p['source']:
    if name == 'namedBt':
        continue
    left = 'wValueVariable' if left == 'namedBt' else left
    right = 'wValueVariable' if right == 'namedBt' else right
    if left in ('wPositive', 'wNegative') or right in ('wPositive', 'wNegative'):
        raise ValueError(('unexpected signed-coordinate use', name))
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
if len(w) != 33 or len(rows) != 143:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; orientation and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 33 variables, 143 live circuit rows; model positivity remains open')
