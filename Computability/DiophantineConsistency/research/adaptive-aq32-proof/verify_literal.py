#!/usr/bin/env python3
"""Check all 142 actual Lean gate rows against the fixed 32-variable graph."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent; R=D.parents[1]
p=R/'research/adaptive-square-sums32-degree6/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='c5b22deb332cc6c9f698864d3d46e1f8d39cca1a2966717d7d319aa3178b9011':raise ValueError('candidate drift')
d=json.loads(raw);source=(R/'Lean/DiophantineConsistency/AdaptiveAQ32Literal.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 32) :=\n');end=source.index('\ntheorem new_literal ',start);block=source[start:end].splitlines()
want=['def literal (p : Fin 4 → ℤ) : Expr (Fin 32) :=']
want += [f'  let {n} : Expr (Fin 32) := .var {i}' for i,n in enumerate(d['witnesses'])]
want += [f'  let {n} : Expr (Fin 32) := .constant (p {i})' for i,n in enumerate(d['fixed_numerals'])]
want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in d['source']]
want += ['  '+d['output']]
if block!=want:
 for i,(x,y) in enumerate(zip(block,want),1):
  if x!=y:raise ValueError(('row mismatch',i,x,y))
 raise ValueError(('row count mismatch',len(block),len(want)))
print('PASS: 32 variables, four ports and all 142 Lean literal gates match the pinned graph')
