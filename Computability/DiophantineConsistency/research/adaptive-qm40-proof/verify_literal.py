#!/usr/bin/env python3
"""Compare the actual 40-variable Lean literal, row by row, to the pinned DAG."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
candidate=D.parent/'adaptive-square-sums40-quotient-quartic/candidate.json'
if hashlib.sha256(candidate.read_bytes()).hexdigest()!='fd49361551fde7c523c4494c2fbfd475f9f6c0b7660e3aef22c09228db82700d':
    raise ValueError('candidate mismatch')
c=json.loads(candidate.read_text())
source=(ROOT/'Lean/DiophantineConsistency/AdaptiveQM40Context.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=\n')
end=source.index('\ntheorem literal_eq ',start)
block=source[start:end].splitlines()
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=']
expected += [f'  let {name} : Expr (Fin 40) := .var {i}' for i,name in enumerate(c['witnesses'])]
expected += [f'  let {name} : Expr (Fin 40) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
expected += ['  add_timeProduct']
if block!=expected:
    for i,(a,b) in enumerate(zip(block,expected),1):
        if a!=b:raise ValueError(('literal row mismatch',i,a,b))
    raise ValueError(('literal row count',len(block),len(expected)))
print('PASS: 40 named variables, 4 ports and all 166 Lean literal rows match the pinned DAG')
