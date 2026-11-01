#!/usr/bin/env python3
"""Check all 148 actual Lean gate rows against the fixed 36-variable graph."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent; R=D.parents[1]
p=R/'research/adaptive-square-sums36/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='5ae497bfdbc9a9394195ec3e20ca79cd749b2361075804ddfdcf920a82dede00':raise ValueError('candidate drift')
d=json.loads(raw);source=(R/'Lean/DiophantineConsistency/AdaptiveAQ36Literal.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 36) :=\n');end=source.index('\ntheorem new_literal ',start);block=source[start:end].splitlines()
want=['def literal (p : Fin 4 → ℤ) : Expr (Fin 36) :=']
want += [f'  let {n} : Expr (Fin 36) := .var {i}' for i,n in enumerate(d['witnesses'])]
want += [f'  let {n} : Expr (Fin 36) := .constant (p {i})' for i,n in enumerate(d['fixed_numerals'])]
want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in d['source']]
want += ['  '+d['output']]
if block!=want:
 for i,(x,y) in enumerate(zip(block,want),1):
  if x!=y:raise ValueError(('row mismatch',i,x,y))
 raise ValueError(('row count mismatch',len(block),len(want)))
print('PASS: 36 variables, four ports and all 148 Lean literal gates match the pinned graph')
