#!/usr/bin/env python3
"""Substitute the V-square coordinate in the degree-six parent DAG."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums36/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != '5ae497bfdbc9a9394195ec3e20ca79cd749b2361075804ddfdcf920a82dede00':
    raise ValueError('parent pin')
p = json.loads(raw)
table = {r[0]: r for r in p['source']}
expected = {'g80': ['g80', '*', 'V', 'V'],
            'squareDifference': ['squareDifference', '-', 'squareVariable', 'g80'],
            'squareConstraint': ['squareConstraint', '*', 'squareDifference', 'squareDifference'],
            'sumWithConstraint': ['sumWithConstraint', '+', 'sumSquares', 'squareConstraint']}
if any(table.get(k) != v for k, v in expected.items()):
    raise ValueError('parent binding differs')
w = [n for n in p['witnesses'] if n != 'squareVariable']
removed = {'squareDifference', 'squareConstraint', 'sumWithConstraint'}
changes = {'squareVariable': 'g80', 'sumWithConstraint': 'sumSquares'}
rows = [[name, op, changes.get(left, left), changes.get(right, right)]
        for name, op, left, right in p['source'] if name not in removed]
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
if len(w) != 35 or len(rows) != 145:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; model zero equivalence and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 35 variables, 145 live circuit rows; model equivalence remains open')
