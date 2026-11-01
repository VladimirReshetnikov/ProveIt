#!/usr/bin/env python3
"""Check the factored square circuit and its degree without expanding its output."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import runpy

D = Path(__file__).resolve().parent
C = D/'candidate.json'
BASE = D.parent/'adaptive-direct-ordinate86'
def require(condition, message):
    if not condition:
        raise RuntimeError(message)
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
require(sha(C) == '11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828', 'candidate pin')
c = json.loads(C.read_text())
p = json.loads((BASE/'candidate.json').read_text())
require(c['parent_sha256'] == sha(BASE/'candidate.json'), 'parent pin')
remove = {'Fs','F0','F1','g86','g87','g88','P13'}
expected = [r for r in p['source'] if r[0] not in remove] + [
 ['auxResidual','-','Fa',1], ['firstSquare','*','A0','A0'],
 ['mainSquare','*','A1','A1'], ['auxSquare','*','auxResidual','auxResidual'],
 ['strongSquare','*','g72','g72'], ['firstMain','+','firstSquare','mainSquare'],
 ['firstMainAux','+','firstMain','auxSquare'], ['sumSquares','+','firstMainAux','strongSquare']]
require(c['source'] == expected and c['output'] == 'sumSquares', 'DAG wiring')
rows = c['source']; available = set(c['witnesses'] + c['fixed_numerals']); table = {}
for name,op,x,y in rows:
    require(name not in available and op in '+-*', ('duplicate or invalid',name))
    require(all(isinstance(z,int) or z in available for z in (x,y)), ('undefined input',name))
    available.add(name); table[name]=(x,y)
live, todo = {'sumSquares'}, ['sumSquares']
while todo:
    for x in table.get(todo.pop(),()):
        if isinstance(x,str) and x not in live:
            live.add(x);todo.append(x)
require(set(table) <= live and set(c['witnesses'] + c['fixed_numerals']) <= live, 'dead gate or input')
require(len(rows) == c['operations'] == 87, 'gate count')
require(dict(sorted(Counter(r[1] for r in rows).items())) == c['operation_breakdown'], 'operation breakdown')
# Re-use the exact sparse integer polynomials that the 86 verifier constructs.
# Check the residual identities explicitly rather than expanding the output.
base = runpy.run_path(str(BASE/'verify_equation86.py'))
checks, g, names = base['checks'], base['g'], base['names']
for factor,gate in [('A','A0'),('L','A1'),('S','g72')]:
    require(checks[factor][0]-1 == g[gate], ('residual polynomial',factor))
require(checks['N'][0] == g['Fa'], 'auxiliary factor polynomial')
polys = [g['A0'],g['A1'],g['Fa']-1,g['g72']]
degrees = [max(sum(k[:13]) for k in poly.d) for poly in polys]
require(degrees == [15,13,18,10], ('residual degrees',degrees))
# A top-degree auxiliary monomial has coefficient exactly beta^8, so it is
# nonzero after specializing beta=(2^47)^2011-1. No other squared residual can
# have degree 36; the square of a nonzero leading polynomial is nonzero over Z.
monomial = {'J':8,'f':6,'X':2,'Y':2}
key = tuple(monomial.get(n,0) for n in names[:13])
coeff = {e[13:]:v for e,v in polys[2].d.items() if e[:13] == key}
require(coeff == {(8,0,0,0):1}, ('leading coefficient',coeff))
require((2**47)**2011-1 > 0, 'positive fixed beta')
print('PASS: 87 live binary operations; residual degrees 15, 13, 18, 10; exact degree 36 after fixing the ports and after positive shift')
