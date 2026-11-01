#!/usr/bin/env python3
"""Check all 141 actual Lean gate rows against the fixed 32-variable graph."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent; R=D.parents[1]
p=R/'research/adaptive-square-sums31-degree6/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='a90ab59a3ab1b3e9b04c2b962ea79c666a3c2dc90e6941c73f5180ab73c5ee67':raise ValueError('candidate drift')
d=json.loads(raw);source=(R/'Lean/DiophantineConsistency/AdaptiveAQ31Literal.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 31) :=\n');end=source.index('\ntheorem new_literal ',start);block=source[start:end].splitlines()
want=['def literal (p : Fin 4 → ℤ) : Expr (Fin 31) :=']
want += [f'  let {n} : Expr (Fin 31) := .var {i}' for i,n in enumerate(d['witnesses'])]
want += [f'  let {n} : Expr (Fin 31) := .constant (p {i})' for i,n in enumerate(d['fixed_numerals'])]
want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in d['source']]
want += ['  '+d['output']]
if block!=want:
 for i,(x,y) in enumerate(zip(block,want),1):
  if x!=y:raise ValueError(('row mismatch',i,x,y))
 raise ValueError(('row count mismatch',len(block),len(want)))
print('PASS: 31 variables, four ports and all 141 Lean literal gates match the pinned graph')
