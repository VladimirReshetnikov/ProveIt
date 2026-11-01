#!/usr/bin/env python3
"""Check all 138 actual Lean gate rows against the fixed 31-variable graph."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent; R=D.parents[1]
p=R/'research/adaptive-square-sums30-degree8/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='f6c88de69011dc070c3cb642cf12bc27bb20c6ee92eaabb56dc1ccd884f685ad':raise ValueError('candidate drift')
d=json.loads(raw);source=(R/'Lean/DiophantineConsistency/AdaptiveAQ30Literal.lean').read_text()
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 30) :=\n');end=source.index('\nend DiophantineConsistency.AdaptiveAQ30Literal',start);block=source[start:end].splitlines()
want=['def literal (p : Fin 4 → ℤ) : Expr (Fin 30) :=']
want += [f'  let {n} : Expr (Fin 30) := .var {i}' for i,n in enumerate(d['witnesses'])]
want += [f'  let {n} : Expr (Fin 30) := .constant (p {i})' for i,n in enumerate(d['fixed_numerals'])]
want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in d['source']]
want += ['  '+d['output']]
if block!=want:
 for i,(x,y) in enumerate(zip(block,want),1):
  if x!=y:raise ValueError(('row mismatch',i,x,y))
 raise ValueError(('row count mismatch',len(block),len(want)))
print('PASS: 30 variables, four ports and all 138 Lean literal gates match the pinned graph')
