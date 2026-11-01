#!/usr/bin/env python3
"""Compare the actual 14-variable Lean literal, row by row, to the pinned DAG."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
candidate=D/'candidate.json'
if hashlib.sha256(candidate.read_bytes()).hexdigest()!='86c765e46d61a85bfa0e84a546136bcb62a9151147d355abde431579d1bd0ffc':
    raise ValueError('candidate mismatch')
c=json.loads(candidate.read_text())
source=(ROOT/'Lean/DiophantineConsistency/AdaptiveRankWitness17.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 17) :=\n')
end=source.index('\ndef embed ',start)
block=source[start:end].splitlines()
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 17) :=']
expected += [f'  let {name} : Expr (Fin 17) := .var {i}' for i,name in enumerate(c['witnesses'])]
expected += [f'  let {name} : Expr (Fin 17) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
expected += ['  finalWithRank']
if block!=expected:
    for i,(a,b) in enumerate(zip(block,expected),1):
        if a!=b:raise ValueError(('literal row mismatch',i,a,b))
    raise ValueError(('literal row count',len(block),len(expected)))
print('PASS: 17 named variables, 4 ports and all 99 Lean literal rows match the pinned DAG')
