#!/usr/bin/env python3
"""Compare the actual 26-variable Lean literal, row by row, to the pinned DAG."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
candidate=D/'candidate.json'
if hashlib.sha256(candidate.read_bytes()).hexdigest()!='4f321364aa9d7fdf91263e174841bb48a441532cce6b8e95b9dc22c4ebc5718a':
    raise ValueError('candidate mismatch')
c=json.loads(candidate.read_text())
source=(ROOT/'Lean/DiophantineConsistency/AdaptiveNamedValues26.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 26) :=\n')
end=source.index('\ndef embed ',start)
block=source[start:end].splitlines()
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 26) :=']
expected += [f'  let {name} : Expr (Fin 26) := .var {i}' for i,name in enumerate(c['witnesses'])]
expected += [f'  let {name} : Expr (Fin 26) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
expected += ['  addCSquare']
if block!=expected:
    for i,(a,b) in enumerate(zip(block,expected),1):
        if a!=b:raise ValueError(('literal row mismatch',i,a,b))
    raise ValueError(('literal row count',len(block),len(expected)))
print('PASS: 26 named variables, 4 ports and all 124 Lean literal rows match the pinned DAG')
