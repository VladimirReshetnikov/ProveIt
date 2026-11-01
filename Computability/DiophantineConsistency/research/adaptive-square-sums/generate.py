#!/usr/bin/env python3
"""Derive the compact sum-of-squares DAG and a definitionally bound Lean literal."""
import hashlib
import json
from collections import Counter
from pathlib import Path

D = Path(__file__).resolve().parent
ROOT = D.parents[1]
PARENT = D.parent/'adaptive-direct-ordinate86/candidate.json'
LEAN = ROOT/'Lean/DiophantineConsistency/AdaptiveDirectOrdinateSquareSumsLiteral.lean'
OUT = D/'candidate.json'

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

require(sha(PARENT) == 'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f', 'parent mismatch')
parent = json.loads(PARENT.read_text())
rows = parent['source']
require(len(rows) == 86, 'parent size')
remove = {'Fs','F0','F1','g86','g87','g88','P13'}
require({row[0] for row in rows if row[0] in remove} == remove, 'removed rows')
new = [row for row in rows if row[0] not in remove]
new += [
    ['auxResidual','-','Fa',1],
    ['firstSquare','*','A0','A0'],
    ['mainSquare','*','A1','A1'],
    ['auxSquare','*','auxResidual','auxResidual'],
    ['strongSquare','*','g72','g72'],
    ['firstMain','+','firstSquare','mainSquare'],
    ['firstMainAux','+','firstMain','auxSquare'],
    ['sumSquares','+','firstMainAux','strongSquare'],
]
names = parent['witnesses'] + parent['fixed_numerals']
known = set(names)
for name, op, a, b in new:
    require(name not in known and op in '+-*', ('bad row', name))
    require(all(isinstance(x,int) or x in known for x in (a,b)), ('bad inputs',name))
    known.add(name)
table = {row[0]:row for row in new}
live, todo = {'sumSquares'}, ['sumSquares']
while todo:
    x = todo.pop()
    if x in table:
        for y in table[x][2:]:
            if isinstance(y,str) and y not in live:
                live.add(y)
                todo.append(y)
require(set(table) <= live and set(names) <= live, 'dead gate or input')
require(len(new) == 87, ('unexpected gate count',len(new)))
counts = dict(sorted(Counter(row[1] for row in new).items()))
data = {'name':'adaptive-direct-ordinate-square-sums-87',
        'scope':'87 live unshifted binary operations; no minimality claim; provenance and proof status in README.',
        'parent_sha256':sha(PARENT), 'witnesses':parent['witnesses'],
        'fixed_numerals':parent['fixed_numerals'], 'source':new, 'output':'sumSquares',
        'operations':len(new), 'operation_breakdown':counts}
OUT.write_text(json.dumps(data,indent=2)+'\n')
lines=['import DiophantineConsistency.AdaptiveDirectOrdinateSquareSums', '',
       '/-! Generated 87-operation DAG, definitionally bound to the optimized sum of squares. -/',
       'set_option autoImplicit false', 'set_option Elab.async false',
       'set_option maxHeartbeats 8000000', 'noncomputable section',
       'namespace DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral',
       'open LO LO.FirstOrder LO.FirstOrder.Arithmetic', 'open scoped LO.FirstOrder.Arithmetic',
       'open AdaptiveEquationSyntax2011 AdaptiveDirectOrdinateSquareSums', '',
       'def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=']
for i, name in enumerate(parent['witnesses']):
    lines.append(f'  let {name} : Expr (Fin 13) := .var {i}')
for i, name in enumerate(parent['fixed_numerals']):
    lines.append(f'  let {name} : Expr (Fin 13) := .constant (p {i})')
lines.extend(f'  let {name} := {a} {op} {b}' for name,op,a,b in new)
lines += ['  sumSquares', '',
          '/-- The generated DAG is exactly the expression used by the zero-set proof. -/',
          'theorem literal_eq_optimized (p : Fin 4 → ℤ) : literal p = optimized p := by',
          '  rfl', '',
          'end DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral', '']
LEAN.write_text('\n'.join(lines))
print('PASS',len(new),'live operations',counts,'candidate',sha(OUT),'Lean literal',sha(LEAN))
