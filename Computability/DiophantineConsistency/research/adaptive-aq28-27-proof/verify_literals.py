#!/usr/bin/env python3
"""Compare draft Lean literal declarations and gates with pinned finite graphs."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
configs=[(28,'adaptive-square-sums28-degree8','6ddad50448c27a371e27cd90f860e30ca8632c57d539f91c2f1c08f10ed1fd27'),(27,'adaptive-square-sums27-degree8','1982b2f164b9b72f965050e3a26cec751f7d0839c2da0cbe3cc020b7e6fc0170')]
for size,path,pin in configs:
 raw=(D.parent/path/'candidate.json').read_bytes()
 if hashlib.sha256(raw).hexdigest()!=pin:raise ValueError('candidate drift')
 d=json.loads(raw);source=(D/'draft-src'/f'AdaptiveAQ{size}Literal.lean').read_text()
 start=source.index(f'def literal (p : Fin 4 → ℤ) : Expr (Fin {size}) :=\n');end=source.index(f'\nend DiophantineConsistency.AdaptiveAQ{size}Literal',start);block=source[start:end].splitlines()
 want=[f'def literal (p : Fin 4 → ℤ) : Expr (Fin {size}) :=']
 want += [f'  let {n} : Expr (Fin {size}) := .var {i}' for i,n in enumerate(d['witnesses'])]
 want += [f'  let {n} : Expr (Fin {size}) := .constant (p {i})' for i,n in enumerate(d['fixed_numerals'])]
 want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in d['source']]
 want += ['  '+d['output']]
 if block!=want:raise ValueError(('literal mismatch',size))
 print(f'PASS: {size} variables, four ports, {len(d["source"])} draft Lean gates match graph; not a Lean compilation')
