#!/usr/bin/env python3
"""Eliminate four named coordinates from the pinned degree-eight AQ26 DAG."""
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is not supported')

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums26-degree8/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != 'd8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5':
    raise ValueError('parent pin')
p = json.loads(raw)
replacements = {'cVariable': 'c', 'productVariable2': 'E',
                'qSquareVariable': 'q2', 'qValueVariable': 'QComputed'}
removed = {
    'cDifference': ['cDifference', '-', 'cVariable', 'c'],
    'cConstraint': ['cConstraint', '*', 'cDifference', 'cDifference'],
    'addC': ['addC', '+', 'finalWithRank', 'cConstraint'],
    'qSquareDifference': ['qSquareDifference', '-', 'qSquareVariable', 'q2'],
    'qSquareConstraint': ['qSquareConstraint', '*', 'qSquareDifference', 'qSquareDifference'],
    'add_qSquare': ['add_qSquare', '+', 'addDELTAConstraint', 'qSquareConstraint'],
    'product2Difference': ['product2Difference', '-', 'productVariable2', 'E'],
    'product2Constraint': ['product2Constraint', '*', 'product2Difference', 'product2Difference'],
    'add_product2': ['add_product2', '+', 'add_qSquare', 'product2Constraint'],
    'qSignedDifference': ['qSignedDifference', '-', 'qValueVariable', 'QComputed'],
    'qSignedConstraint': ['qSignedConstraint', '*', 'qSignedDifference', 'qSignedDifference'],
    'add_qSigned': ['add_qSigned', '+', 'add_product2', 'qSignedConstraint'],
}
table = {row[0]: row for row in p['source']}
if any(table.get(name) != row for name, row in removed.items()):
    raise ValueError('parent residual binding differs')
if p['output'] != 'add_qSigned' or len(p['witnesses']) != 26:
    raise ValueError('parent interface differs')
replacements.update({'addC': 'finalWithRank', 'add_qSquare': 'addDELTAConstraint',
                     'add_product2': 'addDELTAConstraint', 'add_qSigned': 'addDELTAConstraint'})
witnesses = [w for w in p['witnesses'] if w not in replacements]
rows = []
for name, op, left, right in p['source']:
    if name in removed:
        continue
    rows.append([name, op, replacements.get(left, left), replacements.get(right, right)])
if len(witnesses) != 22 or len(rows) != 114:
    raise ValueError(('unexpected graph size', len(witnesses), len(rows)))
known = set(witnesses + p['fixed_numerals'])
for name, op, left, right in rows:
    if (name in known or op not in ('+', '-', '*') or
            any(isinstance(v, str) and v not in known for v in (left, right))):
        raise ValueError(('topology', name))
    known.add(name)
table = {row[0]: row for row in rows}
live = {'addDELTAConstraint'}
todo = list(live)
while todo:
    name = todo.pop()
    if name in table:
        for dep in table[name][2:]:
            if isinstance(dep, str) and dep not in live:
                live.add(dep)
                todo.append(dep)
if set(table) - live or set(witnesses + p['fixed_numerals']) - live:
    raise ValueError('dead row or input')
out = {'scope': 'Candidate only; model and native no-zero equivalence remain open.',
       'witnesses': witnesses, 'fixed_numerals': p['fixed_numerals'],
       'source': rows, 'output': 'addDELTAConstraint', 'operations': len(rows)}
(D / 'candidate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: 22 positive coordinates, 114 live rows; witness transport remains open')
