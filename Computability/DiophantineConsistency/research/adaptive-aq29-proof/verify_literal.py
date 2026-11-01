#!/usr/bin/env python3
"""Check all 135 actual Lean gate rows against the fixed 30-variable graph."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent; R=D.parents[1]
p=R/'research/adaptive-square-sums29-degree8/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='894ff6fa3205629c03de826d8984f4959c2be317bf61c46d0f393f770d113a20':raise ValueError('candidate drift')
d=json.loads(raw);source=(R/'Lean/DiophantineConsistency/AdaptiveAQ29Literal.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 29) :=\n');end=source.index('\nend DiophantineConsistency.AdaptiveAQ29Literal',start);block=source[start:end].splitlines()
want=['def literal (p : Fin 4 → ℤ) : Expr (Fin 29) :=']
want += [f'  let {n} : Expr (Fin 29) := .var {i}' for i,n in enumerate(d['witnesses'])]
want += [f'  let {n} : Expr (Fin 29) := .constant (p {i})' for i,n in enumerate(d['fixed_numerals'])]
want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in d['source']]
want += ['  '+d['output']]
if block!=want:
 for i,(x,y) in enumerate(zip(block,want),1):
  if x!=y:raise ValueError(('row mismatch',i,x,y))
 raise ValueError(('row count mismatch',len(block),len(want)))
print('PASS: 29 variables, four ports and all 135 Lean literal gates match the pinned graph')
