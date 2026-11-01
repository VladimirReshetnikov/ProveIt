#!/usr/bin/env python3
"""Replace the W and root-skew signed pairs with positive coordinates."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums46/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != '7edba2ef3473aad1e54742faf3f9307ef9591b0cd2f05dce65a6497e8425e5a4':
    raise ValueError('parent pin')
p = json.loads(raw)
w = p['witnesses']
if w[18:20] != ['wPositive', 'wNegative'] or w[-2:] != ['rootSkewPositive', 'rootSkewNegative']:
    raise ValueError('unexpected signed coordinates')
w = w[:18] + ['wValueVariable'] + w[20:-2] + ['rootSkewVariable']
table = {r[0]: r for r in p['source']}
expected = {'namedBt': ['namedBt', '-', 'wPositive', 'wNegative'],
            'root_skew': ['root_skew', '-', 'rootSkewPositive', 'rootSkewNegative'],
            'root_skewComputed': ['root_skewComputed', '*', 'k', 'namedBt'],
            'wDifference': ['wDifference', '-', 'namedBt', 'Bt'],
            'rootSkewDifference': ['rootSkewDifference', '-', 'root_skew', 'root_skewComputed']}
if any(table.get(k) != v for k, v in expected.items()):
    raise ValueError('parent binding differs')
replace = {'namedBt': 'wValueVariable', 'root_skew': 'rootSkewVariable'}
rows = []
for name, op, left, right in p['source']:
    if name in replace:
        continue
    left, right = replace.get(left, left), replace.get(right, right)
    if left in ('wPositive', 'wNegative', 'rootSkewPositive', 'rootSkewNegative') or right in ('wPositive', 'wNegative', 'rootSkewPositive', 'rootSkewNegative'):
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
if len(w) != 44 or len(rows) != 176:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; W/root-skew positivity and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 44 variables, 176 live circuit rows; W positivity remains open')
