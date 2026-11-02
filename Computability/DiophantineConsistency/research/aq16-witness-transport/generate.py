#!/usr/bin/env python3
"""Generate AQ16's literal and sum-of-squares decomposition from the pinned graph."""
import hashlib
import json
from pathlib import Path
if not __debug__: raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
G=D.parent/'aq17-positive-signed-binding/candidate16.json'
T=ROOT/'research/aq17-witness-transport/draft-src/AdaptiveAQ17Zeros.lean'
assert hashlib.sha256(G.read_bytes()).hexdigest()=='a7d6f8a618a810b37eb7a9de6bd92ceb73bd6351971fdd39045bf95f8bf9edac'
assert hashlib.sha256(T.read_bytes()).hexdigest()=='09f5d841570b003ddff1fc13edd66b8d6236a4b7e63a6a904a4b53a47a9fd565'
c=json.loads(G.read_text()); assert len(c['witnesses'])==16 and len(c['source'])==96
factors=['A0','A1','auxResidual','g72','rankDifference','zDifference','vDifference']
assert c['residuals']==factors
out=D/'draft-src';out.mkdir(exist_ok=True)
def bindings(rows):
 return (''.join(f'  let {name} : Expr (Fin 16) := .var {i}\n' for i,name in enumerate(c['witnesses']))+
         ''.join(f'  let {name} : Expr (Fin 16) := .constant (p {i})\n' for i,name in enumerate(c['fixed_numerals']))+
         ''.join(f'  let {name} := {a} {op} {b}\n' for name,op,a,b in rows))
lit=('import DiophantineConsistency.AdaptiveAQ17Literal\nset_option autoImplicit false\nnoncomputable section\n'
     'namespace DiophantineConsistency.AdaptiveAQ16Literal\nopen AdaptiveEquationSyntax2011\n'
     'def literal (p : Fin 4 → ℤ) : Expr (Fin 16) :=\n'+bindings(c['source'])+
     f"  {c['output']}\nend DiophantineConsistency.AdaptiveAQ16Literal\n")
(out/'AdaptiveAQ16Literal.lean').write_text(lit)
rows={r[0]:r for r in c['source']};live=set(factors);todo=list(live)
while todo:
 name=todo.pop()
 if name in rows:
  for dep in rows[name][2:]:
   if isinstance(dep,str) and dep not in live:live.add(dep);todo.append(dep)
selected=[r for r in c['source'] if r[0] in live]
base=T.read_text()
pre=base[:base.index('def residuals')].replace('AdaptiveAQ17Literal','AdaptiveAQ16Literal').replace('AdaptiveAQ17Zeros','AdaptiveAQ16Zeros')
middle='def residuals (p : Fin 4 → ℤ) : Fin 7 → Expr (Fin 16) :=\n'+bindings(selected)+'  !['+','.join(factors)+']\n'
middle+='def sum (p : Fin 4 → ℤ) : Expr (Fin 16) := '+' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(7))+'\n'
tail=(base[base.index('theorem sum_shape'):].replace('AdaptiveAQ17Literal','AdaptiveAQ16Literal')
      .replace('AdaptiveAQ17Zeros','AdaptiveAQ16Zeros').replace('Fin 17','Fin 16')
      .replace('Fin 8','__RESIDUALS__').replace('Fin 7','Fin 6').replace('__RESIDUALS__','Fin 7'))
(out/'AdaptiveAQ16Zeros.lean').write_text(pre+middle+tail)
print('Generated AQ16 literal and zeros from pinned graph.')
