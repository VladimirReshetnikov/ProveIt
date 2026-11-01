#!/usr/bin/env python3
"""Remove four positive product/square coordinates from the degree-six DAG."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums40/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != 'd02609f153f86f4ef73ca077f0aaef171ca779ead3013131fa13aa187656de37':
    raise ValueError('parent pin')
p = json.loads(raw)
sub = {'cubeVariable': 'q3', 'productVariable': 'g55',
       'psiSquareVariable': 'g39', 'ySquareVariable': 'y2'}
labels = {'cube': 'cubeVariable', 'product': 'productVariable',
          'psiSquare': 'psiSquareVariable', 'ySquare': 'ySquareVariable'}
table = {r[0]: r for r in p['source']}
definitions = {'q3': ['q3', '*', 'q', 'qSquareVariable'],
               'g55': ['g55', '*', 'productVariable2', 'q'],
               'g39': ['g39', '*', 'scaleVariable', 'scaleVariable'],
               'y2': ['y2', '*', 'y', 'y']}
for name, row in definitions.items():
    if table.get(name) != row:
        raise ValueError(('definition differs', name))
for label, variable in labels.items():
    if table.get(label + 'Difference') != [label + 'Difference', '-', variable, sub[variable]]:
        raise ValueError(('difference differs', label))
    if table.get(label + 'Constraint') != [label + 'Constraint', '*', label + 'Difference', label + 'Difference']:
        raise ValueError(('square differs', label))
accum = {'addCube': ['addCube', '+', 'finalWithNamedValues', 'cubeConstraint'],
         'addProduct': ['addProduct', '+', 'addCube', 'productConstraint'],
         'add_psiSquare': ['add_psiSquare', '+', 'add_product2', 'psiSquareConstraint'],
         'add_ySquare': ['add_ySquare', '+', 'add_scaledIndex', 'ySquareConstraint']}
if any(table.get(k) != v for k, v in accum.items()):
    raise ValueError('accumulation differs')
replace = dict(sub, addCube='finalWithNamedValues', addProduct='finalWithNamedValues',
               add_psiSquare='add_product2', add_ySquare='add_scaledIndex')
removed = set(accum)
for label in labels:
    removed.update([label + 'Difference', label + 'Constraint'])
w = [name for name in p['witnesses'] if name not in sub]
rows = []
for name, op, left, right in p['source']:
    if name not in removed:
        rows.append([name, op, replace.get(left, left), replace.get(right, right)])
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
if len(w) != 36 or len(rows) != 148:
    raise ValueError('unexpected size')
out = {'scope': 'Candidate only; model zero equivalence and native iPRA transfer remain open.',
       'witnesses': w, 'fixed_numerals': p['fixed_numerals'], 'source': rows,
       'output': p['output'], 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 36 variables, 148 live circuit rows; model equivalence remains open')
