#!/usr/bin/env python3
"""Replace the signed Z pair with a single positive coordinate."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums35/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != 'bb3c4a0a02b2735e3726071cdeb480f35a059905a3204d4569ac0eaaa1abd44d':
    raise ValueError('parent pin')
p = json.loads(raw)
w = p['witnesses']
if w[22:24] != ['zPositive', 'zNegative']:
    raise ValueError('unexpected Z coordinates')
w = w[:22] + ['zValueVariable'] + w[24:]
table = {r[0]: r for r in p['source']}
expected = {'Z': ['Z', '-', 'zPositive', 'zNegative'],
            'g38': ['g38', '*', 'Z', 'Z'],
            'zDifference': ['zDifference', '-', 'Z', 'ZComputed'],
            'g31': ['g31', '+', 'g30', 'r'],
            'g39': ['g39', '*', 'scaleVariable', 'scaleVariable']}
if any(table.get(k) != v for k, v in expected.items()):
    raise ValueError('parent binding differs')
rows = []
for name, op, left, right in p['source']:
    if name == 'Z':
        continue
    left = 'zValueVariable' if left == 'Z' else left
    right = 'zValueVariable' if right == 'Z' else right
    if left in ('zPositive', 'zNegative') or right in ('zPositive', 'zNegative'):
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
if len(w) != 34 or len(rows) != 144:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; orientation and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 34 variables, 144 live circuit rows; model orientation remains open')
