#!/usr/bin/env python3
"""Compare the actual 42-variable Lean literal, row by row, to the pinned DAG."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
candidate=D.parent/'adaptive-square-sums42-quartic/candidate.json'
if hashlib.sha256(candidate.read_bytes()).hexdigest()!='98e9d64a3c15b168c9a0cbcd813abd05d11cea627c5b8c9de004d493ed9453f3':
    raise ValueError('candidate mismatch')
c=json.loads(candidate.read_text())
source=(ROOT/'Lean/DiophantineConsistency/AdaptiveQV42Context.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 42) :=\n')
end=source.index('\ntheorem old_literal ',start)
block=source[start:end].splitlines()
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 42) :=']
expected += [f'  let {name} : Expr (Fin 42) := .var {i}' for i,name in enumerate(c['witnesses'])]
expected += [f'  let {name} : Expr (Fin 42) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
expected += ['  add_timeProduct']
if block!=expected:
    for i,(a,b) in enumerate(zip(block,expected),1):
        if a!=b:raise ValueError(('literal row mismatch',i,a,b))
    raise ValueError(('literal row count',len(block),len(expected)))
print('PASS: 42 named variables, 4 ports and all 174 Lean literal rows match the pinned DAG')
