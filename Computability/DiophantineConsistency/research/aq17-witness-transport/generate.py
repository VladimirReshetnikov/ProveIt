#!/usr/bin/env python3
"""Generate AQ17's literal and sum-of-squares decomposition from the pinned graph."""
import hashlib
import json
from pathlib import Path
if not __debug__: raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
G=D.parent/'aq22-positive-binding-survey/candidate17.json'
T=ROOT/'reviews/ipra-aq22-guarded-author/src/DiophantineConsistency/AdaptiveAQ22Zeros.lean'
assert hashlib.sha256(G.read_bytes()).hexdigest()=='760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
assert hashlib.sha256(T.read_bytes()).hexdigest()=='68f5256462721aac705c867a3ca7f3d2b39064e85e90d0f72dd7d2198c522f6d'
c=json.loads(G.read_text()); assert len(c['witnesses'])==17 and len(c['source'])==99
factors=['A0','A1','auxResidual','g72','rankDifference','zDifference','dDifference','vDifference']
assert c['residuals']==factors
out=D/'draft-src';out.mkdir(exist_ok=True)
def bindings(rows):
 return (''.join(f'  let {name} : Expr (Fin 17) := .var {i}\n' for i,name in enumerate(c['witnesses']))+
         ''.join(f'  let {name} : Expr (Fin 17) := .constant (p {i})\n' for i,name in enumerate(c['fixed_numerals']))+
         ''.join(f'  let {name} := {a} {op} {b}\n' for name,op,a,b in rows))
lit=('import DiophantineConsistency.AdaptiveAQ22Literal\nset_option autoImplicit false\nnoncomputable section\n'
     'namespace DiophantineConsistency.AdaptiveAQ17Literal\nopen AdaptiveEquationSyntax2011\n'
     'def literal (p : Fin 4 → ℤ) : Expr (Fin 17) :=\n'+bindings(c['source'])+
     f"  {c['output']}\nend DiophantineConsistency.AdaptiveAQ17Literal\n")
(out/'AdaptiveAQ17Literal.lean').write_text(lit)
rows={r[0]:r for r in c['source']};live=set(factors);todo=list(live)
while todo:
 name=todo.pop()
 if name in rows:
  for dep in rows[name][2:]:
   if isinstance(dep,str) and dep not in live:live.add(dep);todo.append(dep)
selected=[r for r in c['source'] if r[0] in live]
base=T.read_text()
pre=base[:base.index('def residuals')].replace('AdaptiveAQ22Literal','AdaptiveAQ17Literal').replace('AdaptiveAQ22Zeros','AdaptiveAQ17Zeros')
middle='def residuals (p : Fin 4 → ℤ) : Fin 8 → Expr (Fin 17) :=\n'+bindings(selected)+'  !['+','.join(factors)+']\n'
middle+='def sum (p : Fin 4 → ℤ) : Expr (Fin 17) := '+' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(8))+'\n'
tail=(base[base.index('theorem sum_shape'):].replace('AdaptiveAQ22Literal','AdaptiveAQ17Literal')
      .replace('AdaptiveAQ22Zeros','AdaptiveAQ17Zeros').replace('Fin 22','Fin 17').replace('Fin 13','Fin 8').replace('Fin 12','Fin 7'))
(out/'AdaptiveAQ17Zeros.lean').write_text(pre+middle+tail)
print('Generated AQ17 literal and zeros from pinned graph.')
