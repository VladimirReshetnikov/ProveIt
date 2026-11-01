#!/usr/bin/env python3
"""Replace the signed D pair with a single positive coordinate."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums44/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != '64cb66826c91199671e60c2fce8906e64028a60a6f133feecc7c9ce96ba91fec':
    raise ValueError('parent pin')
p = json.loads(raw)
w = p['witnesses']
if w[24:26] != ['dPositive', 'dNegative']:
    raise ValueError('unexpected D coordinates')
w = w[:24] + ['dValueVariable'] + w[26:]
table = {r[0]: r for r in p['source']}
expected = {'Dstar': ['Dstar', '-', 'dPositive', 'dNegative'],
            'g61': ['g61', '*', 'Dstar', 'Dstar'],
            'dDifference': ['dDifference', '-', 'Dstar', 'DstarComputed']}
if any(table.get(k) != v for k, v in expected.items()):
    raise ValueError('parent binding differs')
rows = []
for name, op, left, right in p['source']:
    if name == 'Dstar':
        continue
    left = 'dValueVariable' if left == 'Dstar' else left
    right = 'dValueVariable' if right == 'Dstar' else right
    if left in ('dPositive', 'dNegative') or right in ('dPositive', 'dNegative'):
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
if len(w) != 43 or len(rows) != 175:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; main-root positivity and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 43 variables, 175 live circuit rows; main-root positivity remains open')
