#!/usr/bin/env python3
"""Compare the actual 14-variable Lean literal, row by row, to the pinned DAG."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
candidate=D/'candidate.json'
if hashlib.sha256(candidate.read_bytes()).hexdigest()!='0c7451eaadba5569f2d901867c3e80deb0663e09bd51dd6972d1949eb1f669af':
    raise ValueError('candidate mismatch')
c=json.loads(candidate.read_text())
source=(ROOT/'Lean/DiophantineConsistency/AdaptiveSquareWitness14.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 14) :=\n')
end=source.index('\ndef embed ',start)
block=source[start:end].splitlines()
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 14) :=']
expected += [f'  let {name} : Expr (Fin 14) := .var {i}' for i,name in enumerate(c['witnesses'])]
expected += [f'  let {name} : Expr (Fin 14) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
expected += ['  sumWithConstraint']
if block!=expected:
    for i,(a,b) in enumerate(zip(block,expected),1):
        if a!=b:raise ValueError(('literal row mismatch',i,a,b))
    raise ValueError(('literal row count',len(block),len(expected)))
print('PASS: 14 named variables, 4 ports and all 91 Lean literal rows match the pinned DAG')
