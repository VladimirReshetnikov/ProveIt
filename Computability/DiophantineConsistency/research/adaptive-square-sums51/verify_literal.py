#!/usr/bin/env python3
"""Compare the actual 51-variable Lean literal, row by row, to the pinned DAG."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
candidate=D/'candidate.json'
if hashlib.sha256(candidate.read_bytes()).hexdigest()!='f29404f0fb2581f8fe28fb1c1537d1236696ac3580c9e9b5c1edd347b4385c72':
    raise ValueError('candidate mismatch')
c=json.loads(candidate.read_text())
source=(ROOT/'Lean/DiophantineConsistency/AdaptiveNamedValues51.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 51) :=\n')
end=source.index('\ndef embed ',start)
block=source[start:end].splitlines()
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 51) :=']
expected += [f'  let {name} : Expr (Fin 51) := .var {i}' for i,name in enumerate(c['witnesses'])]
expected += [f'  let {name} : Expr (Fin 51) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
expected += ['  add_timeProduct']
if block!=expected:
    for i,(a,b) in enumerate(zip(block,expected),1):
        if a!=b:raise ValueError(('literal row mismatch',i,a,b))
    raise ValueError(('literal row count',len(block),len(expected)))
print('PASS: 51 named variables, 4 ports and all 187 Lean literal rows match the pinned DAG')
