#!/usr/bin/env python3
"""Prepare the AQ22 literal and zero-decomposition Lean drafts from the pinned graph."""
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]; SOURCE=ROOT/'Lean/DiophantineConsistency'; LEAN=D/'draft-src'; LEAN.mkdir(exist_ok=True)
configs=[(22,26,'adaptive-square-sums22-degree10','1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106',None)]
factors=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
base_bytes=(SOURCE/'AdaptiveAQ29Zeros.lean').read_bytes()
if hashlib.sha256(base_bytes).hexdigest()!='d83579a4b27e4b55d7ad67afb07a95c0235460d97152c10201e8291de8971be7':
 raise ValueError('AQ29 zero template drift')
base=base_bytes.decode()
for n,parent,path,pin,removed in configs:
 raw=(D.parent/path/'candidate.json').read_bytes()
 if hashlib.sha256(raw).hexdigest()!=pin:raise ValueError('graph pin')
 c=json.loads(raw)
 def bindings(rows):
  names=''.join(f'  let {name} : Expr (Fin {n}) := .var {i}\n' for i,name in enumerate(c['witnesses']))
  names+=''.join(f'  let {name} : Expr (Fin {n}) := .constant (p {i})\n' for i,name in enumerate(c['fixed_numerals']))
  return names+''.join(f'  let {name} := {a} {op} {b}\n' for name,op,a,b in rows)
 lit=f'import DiophantineConsistency.AdaptiveAQ{parent}Literal\nset_option autoImplicit false\nnoncomputable section\nnamespace DiophantineConsistency.AdaptiveAQ{n}Literal\nopen AdaptiveEquationSyntax2011\ndef literal (p : Fin 4 → ℤ) : Expr (Fin {n}) :=\n'+bindings(c['source'])+f"  {c['output']}\nend DiophantineConsistency.AdaptiveAQ{n}Literal\n"
 (LEAN/f'AdaptiveAQ{n}Literal.lean').write_text(lit)
 rows={row[0]:row for row in c['source']}; live=set(factors);todo=list(live)
 while todo:
  a=todo.pop()
  if a in rows:
   for dep in rows[a][2:]:
    if isinstance(dep,str) and dep not in live:live.add(dep);todo.append(dep)
 selected=[r for r in c['source'] if r[0] in live]
 pre=base[:base.index('def residuals')].replace('AdaptiveAQ29Literal',f'AdaptiveAQ{n}Literal').replace('AdaptiveAQ29Zeros',f'AdaptiveAQ{n}Zeros')
 parts=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(len(factors)))
 middle=f'def residuals (p : Fin 4 → ℤ) : Fin {len(factors)} → Expr (Fin {n}) :=\n'+bindings(selected)+'  !['+','.join(factors)+']\n'+f'def sum (p : Fin 4 → ℤ) : Expr (Fin {n}) := {parts}\n'
 # Use placeholders so AQ28's 20→19 result is not then rewritten to 18.
 tail=(base[base.index('theorem sum_shape'):]
       .replace('AdaptiveAQ29Literal',f'AdaptiveAQ{n}Literal')
       .replace('AdaptiveAQ29Zeros',f'AdaptiveAQ{n}Zeros')
       .replace('Fin 29',f'Fin {n}')
       .replace('Fin 20','__RESIDUAL_ARITY__')
       .replace('Fin 19',f'Fin {len(factors)-1}')
       .replace('__RESIDUAL_ARITY__',f'Fin {len(factors)}'))
 (LEAN/f'AdaptiveAQ{n}Zeros.lean').write_text(pre+middle+tail)
 print(f'Prepared AQ{n} literal and zero decomposition; compilation pending')
