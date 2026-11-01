#!/usr/bin/env python3
"""Compare the actual 41-variable Lean literal, row by row, to the pinned DAG."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
candidate=D.parent/'adaptive-square-sums41-quartic/candidate.json'
if hashlib.sha256(candidate.read_bytes()).hexdigest()!='62e7851fa8cfee544f92b83ff4f422e200f10c4a45f0e236d83e1ac3f07dd239':
    raise ValueError('candidate mismatch')
c=json.loads(candidate.read_text())
source=(ROOT/'Lean/DiophantineConsistency/AdaptiveQF41Context.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 41) :=\n')
end=source.index('\ntheorem literal_eq ',start)
block=source[start:end].splitlines()
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 41) :=']
expected += [f'  let {name} : Expr (Fin 41) := .var {i}' for i,name in enumerate(c['witnesses'])]
expected += [f'  let {name} : Expr (Fin 41) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
expected += ['  add_timeProduct']
if block!=expected:
    for i,(a,b) in enumerate(zip(block,expected),1):
        if a!=b:raise ValueError(('literal row mismatch',i,a,b))
    raise ValueError(('literal row count',len(block),len(expected)))
print('PASS: 41 named variables, 4 ports and all 170 Lean literal rows match the pinned DAG')
