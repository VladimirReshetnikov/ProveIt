#!/usr/bin/env python3
"""Check all 160 actual Lean gate rows against the fixed 40-variable graph."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent; R=D.parents[1]
p=R/'research/adaptive-square-sums40/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='d02609f153f86f4ef73ca077f0aaef171ca779ead3013131fa13aa187656de37':raise ValueError('candidate drift')
d=json.loads(raw);source=(R/'Lean/DiophantineConsistency/AdaptiveAQ40Literal.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=\n');end=source.index('\ntheorem new_literal ',start);block=source[start:end].splitlines()
want=['def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=']
want += [f'  let {n} : Expr (Fin 40) := .var {i}' for i,n in enumerate(d['witnesses'])]
want += [f'  let {n} : Expr (Fin 40) := .constant (p {i})' for i,n in enumerate(d['fixed_numerals'])]
want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in d['source']]
want += ['  '+d['output']]
if block!=want:
 for i,(x,y) in enumerate(zip(block,want),1):
  if x!=y:raise ValueError(('row mismatch',i,x,y))
 raise ValueError(('row count mismatch',len(block),len(want)))
print('PASS: 40 variables, four ports and all 160 Lean literal gates match the pinned graph')
