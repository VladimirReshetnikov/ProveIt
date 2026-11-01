#!/usr/bin/env python3
"""Replace the signed V pair with a single positive coordinate."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums32-degree6/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != 'c5b22deb332cc6c9f698864d3d46e1f8d39cca1a2966717d7d319aa3178b9011':
    raise ValueError('parent pin')
p = json.loads(raw)
w = p['witnesses']
if w[23:25] != ['vPositive', 'vNegative']:
    raise ValueError('unexpected V coordinates')
w = w[:23] + ['vValueVariable'] + w[25:]
table = {r[0]: r for r in p['source']}
expected = {'V': ['V', '-', 'vPositive', 'vNegative'],
            'g80': ['g80', '*', 'V', 'V'],
            'vDifference': ['vDifference', '-', 'V', 'VComputed']}
if any(table.get(k) != v for k, v in expected.items()):
    raise ValueError('parent binding differs')
rows = []
for name, op, left, right in p['source']:
    if name == 'V':
        continue
    left = 'vValueVariable' if left == 'V' else left
    right = 'vValueVariable' if right == 'V' else right
    if left in ('vPositive', 'vNegative') or right in ('vPositive', 'vNegative'):
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
if len(w) != 31 or len(rows) != 141:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; orientation and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 31 variables, 141 live circuit rows; model orientation remains open')
