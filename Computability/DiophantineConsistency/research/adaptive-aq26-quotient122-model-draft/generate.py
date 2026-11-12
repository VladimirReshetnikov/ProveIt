#!/usr/bin/env python3
"""Reconstruct and compare inert two-quotient literal/residual source; no Lean or writes."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
g=json.loads(pin(D/'research/adaptive-aq26-two-quotients122/candidate.json','14c9cac4f3af45c15ec5e6df623c83fcab7581ba042aff34c6614dad890154ae'))
old=pin(D/'Lean/DiophantineConsistency/AdaptiveAQ26Zeros.lean','dd49ed0bf68338354dd99498cb091176e21eed281dff0fe252ed8fc99932024c')
x=re.findall(r'^  !\[([^\n]+)\]$',old,re.M);assert len(x)==1;res=x[0].split(',');assert len(res)==17 and res[:2]==['A0','A1']
assert len(g['witnesses'])==26 and len(g['source'])==g['operations']==122
names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']];assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in names)
L=['  let '+n+' : Expr (Fin 26) := .var '+str(i) for i,n in enumerate(g['witnesses'])]+['  let '+n+' : Expr (Fin 26) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]+['  let '+n+' := '+str(a)+' '+o+' '+str(b) for n,o,a,b in g['source']];body='\n'.join(L)
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
lit='import DiophantineConsistency.AdaptiveAQ26Literal\n\n'+pre+'namespace DiophantineConsistency.AQ26Quotient122LiteralDraft\nopen AdaptiveEquationSyntax2011\n\ndef literal (p : Fin 4 → ℤ) : Expr (Fin 26) :=\n'+body+'\n  '+g['output']+'\n\nend DiophantineConsistency.AQ26Quotient122LiteralDraft\n'
assert (P/'AQ26Quotient122Literal.lean.src').read_text() == lit
sumexpr=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(17))
rs='import AQ26Quotient122Literal\n\n'+pre+'namespace DiophantineConsistency.AQ26Quotient122ResidualsDraft\nopen AdaptiveEquationSyntax2011\n\ndef residuals (p : Fin 4 → ℤ) : Fin 17 → Expr (Fin 26) :=\n'+body+'\n  !['+','.join(res)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 26) := '+sumexpr+'''\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = AQ26Quotient122LiteralDraft.literal p := by rfl
end DiophantineConsistency.AQ26Quotient122ResidualsDraft
#print axioms DiophantineConsistency.AQ26Quotient122ResidualsDraft.sum_eq_literal
'''
assert (P/'AQ26Quotient122Residuals.lean.src').read_text() == rs
print(json.dumps({'scope':'inert literal and ordered sum source; no Lean','rows':122,'variables':26,'residuals':17,'sum_exact_syntax_DAG':True,'literal_sha256':hashlib.sha256(lit.encode()).hexdigest(),'residual_sha256':hashlib.sha256(rs.encode()).hexdigest()},sort_keys=True,indent=2))
