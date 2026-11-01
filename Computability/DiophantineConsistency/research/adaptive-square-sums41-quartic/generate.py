#!/usr/bin/env python3
"""Replace the scaled first root by its positive quotient."""
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
raw = (D.parent / 'adaptive-square-sums42-quartic/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != '98e9d64a3c15b168c9a0cbcd813abd05d11cea627c5b8c9de004d493ed9453f3':
    raise ValueError('parent pin')
p = json.loads(raw)
w = p['witnesses']
if w[23] != 'zValueVariable' or w[29] != 'psiSquareVariable':
    raise ValueError('unexpected first-root coordinates')
w = ['firstQuotient' if name == 'zValueVariable' else name for name in w if name != 'psiSquareVariable']
expected = {'g38': ['g38','*','zValueVariable','zValueVariable'],
 'g39': ['g39','*','scaleVariable','scaleVariable'],
 'g41': ['g41','+',1,'ellProductVariable'], 'g42':['g42','*','psiSquareVariable','g41'],
 'A0':['A0','-','g38','g42'], 'zDifference':['zDifference','-','zValueVariable','ZComputed'],
 'psiSquareDifference':['psiSquareDifference','-','psiSquareVariable','g39'],
 'psiSquareConstraint':['psiSquareConstraint','*','psiSquareDifference','psiSquareDifference'],
 'add_psiSquare':['add_psiSquare','+','add_product2','psiSquareConstraint'],
 'add_ellProduct':['add_ellProduct','+','add_psiSquare','ellProductConstraint']}
table = {r[0]:r for r in p['source']}
if any(table.get(k) != v for k,v in expected.items()):
    raise ValueError('parent bindings changed')
rows = []
for name,op,left,right in p['source']:
    if name in {'g39','g42','psiSquareDifference','psiSquareConstraint','add_psiSquare'}:
        continue
    if name == 'zDifference':
        rows.append(['zScaled','*','scaleVariable','firstQuotient'])
        left = 'zScaled'
    if name == 'A0':
        right = 'g41'
    if name == 'add_ellProduct':
        left = 'add_product2'
    left = 'firstQuotient' if left == 'zValueVariable' else left
    right = 'firstQuotient' if right == 'zValueVariable' else right
    rows.append([name,op,left,right])
table = {r[0]:r for r in rows}
known = set(w+p['fixed_numerals'])
for name,op,left,right in rows:
    if name in known or any(isinstance(x,str) and x not in known for x in (left,right)):
        raise ValueError(('invalid topological row',name))
    known.add(name)
live={p['output']};todo=list(live)
while todo:
    name=todo.pop()
    if name in table:
        for x in table[name][2:]:
            if isinstance(x,str) and x not in live:
                live.add(x);todo.append(x)
if not set(table) <= live or not set(w+p['fixed_numerals']) <= live:
    raise ValueError('dead node or input')
if len(w)!=41 or len(rows)!=170:
    raise ValueError(('unexpected graph size',len(w),len(rows)))
out={'scope':'Candidate only; quotient transport and native iPRA endpoint remain open.',
     'witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,
     'output':p['output'],'operations':len(rows)}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 41 variables, 170 live arithmetic rows; quotient transport remains open')
