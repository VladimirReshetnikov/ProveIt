#!/usr/bin/env python3
"""Reconstruct and compare inert two-quotient literal/residual source; no Lean or writes."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
g=json.loads(pin(D/'research/adaptive-aq20-substituted-scales104/candidate.json','e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'))
old=pin(D/'Lean/DiophantineConsistency/AdaptiveAQ22Zeros.lean','68f5256462721aac705c867a3ca7f3d2b39064e85e90d0f72dd7d2198c522f6d')
x=re.findall(r'^  !\[([^\n]+)\]$',old,re.M);assert len(x)==1;res=x[0].split(',');assert len(res)==13 and res[:2]==['A0','A1']; res=res[:4]+res[6:]
assert len(g['witnesses'])==20 and len(g['source'])==g['operations']==104
names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']];assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in names)
L=['  let '+n+' : Expr (Fin 20) := .var '+str(i) for i,n in enumerate(g['witnesses'])]+['  let '+n+' : Expr (Fin 20) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]+['  let '+n+' := '+str(a)+' '+o+' '+str(b) for n,o,a,b in g['source']];body='\n'.join(L)
env={x:('leaf',x) for x in g['witnesses']+g['fixed_numerals']}
def val(x):return ('constant',x) if type(x)==int else env[x]
for n,o,a,b in g['source']:env[n]=(o,val(a),val(b))
total=None
for n in res:
 sq=('*',env[n],env[n]);total=sq if total is None else ('+',total,sq)
assert total==env[g['output']]
pre='''/-! Generated inert source; no Lean elaboration. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
'''
lit='import AQ22Quotient110Literal\n\n'+pre+'namespace DiophantineConsistency.AQ20Substituted104LiteralDraft\nopen AdaptiveEquationSyntax2011\n\ndef literal (p : Fin 4 → ℤ) : Expr (Fin 20) :=\n'+body+'\n  '+g['output']+'\n\nend DiophantineConsistency.AQ20Substituted104LiteralDraft\n'
assert (P/'AQ20Substituted104Literal.lean.src').read_text() == lit
sumexpr=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(11))
rs='import AQ20Substituted104Literal\n\n'+pre+'namespace DiophantineConsistency.AQ20Substituted104ResidualsDraft\nopen AdaptiveEquationSyntax2011\n\ndef residuals (p : Fin 4 → ℤ) : Fin 17 → Expr (Fin 20) :=\n'+body+'\n  !['+','.join(res)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 20) := '+sumexpr+'''\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = AQ20Substituted104LiteralDraft.literal p := by rfl
end DiophantineConsistency.AQ20Substituted104ResidualsDraft
#print axioms DiophantineConsistency.AQ20Substituted104ResidualsDraft.sum_eq_literal
'''
assert (P/'AQ20Substituted104Residuals.lean.src').read_text() == rs
print(json.dumps({'scope':'inert literal and ordered sum source; no Lean','rows':104,'variables':20,'residuals':11,'sum_exact_syntax_DAG':True,'literal_sha256':hashlib.sha256(lit.encode()).hexdigest(),'residual_sha256':hashlib.sha256(rs.encode()).hexdigest()},sort_keys=True,indent=2))
