#!/usr/bin/env python3
"""Compare the actual 46-variable Lean literal, row by row, to the pinned DAG."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
candidate=D/'candidate.json'
if hashlib.sha256(candidate.read_bytes()).hexdigest()!='7edba2ef3473aad1e54742faf3f9307ef9591b0cd2f05dce65a6497e8425e5a4':
    raise ValueError('candidate mismatch')
c=json.loads(candidate.read_text())
source=(ROOT/'Lean/DiophantineConsistency/AdaptiveZ46Context.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 46) :=\n')
end=source.index('\ntheorem old_literal ',start)
block=source[start:end].splitlines()
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 46) :=']
expected += [f'  let {name} : Expr (Fin 46) := .var {i}' for i,name in enumerate(c['witnesses'])]
expected += [f'  let {name} : Expr (Fin 46) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
expected += ['  add_timeProduct']
if block!=expected:
    for i,(a,b) in enumerate(zip(block,expected),1):
        if a!=b:raise ValueError(('literal row mismatch',i,a,b))
    raise ValueError(('literal row count',len(block),len(expected)))
print('PASS: 46 named variables, 4 ports and all 178 Lean literal rows match the pinned DAG')
