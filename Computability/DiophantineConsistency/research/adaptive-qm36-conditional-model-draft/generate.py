#!/usr/bin/env python3
"""Generate inert 155/153 literals and residual vectors; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
graphs=[('155',json.loads(pin(D/'research/adaptive-square-sums36-combined-shift-quartic/candidate.json','dfa54188a5457f6de2e6d232b2141f12e5f38406bea88e0a5f3f8a07def78523'))),('153',json.loads(pin(D/'research/adaptive-square-sums36-factored-roots/candidate.json','92ec1caec949f4cad0cc3e021becfbbb04a971403a76b282d240addc58d58182')))]
old=pin(D/'research/adaptive-qm37-conditional-model-draft/AdaptiveQM37Residuals.lean.src','c1c0801c89f701b69b244dfed8c95ab5d289d1b309cb5e98fe28b064644efe3a')
x=re.findall(r'^  !\[([^\n]+)\]$',old,re.M);assert len(x)==1;prior=x[0].split(',');assert len(prior)==28 and prior[11]=='productDifference' and prior[26]=='gammaProductDifference'
res=[('combinedEquality' if i==11 else n) for i,n in enumerate(prior) if i!=26];assert len(res)==27
outputs={}
for suffix,g in graphs:
 assert len(g['witnesses'])==36 and len(g['source'])==int(suffix)
 names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']];assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in names)
 L=['  let '+n+' : Expr (Fin 36) := .var '+str(i) for i,n in enumerate(g['witnesses'])]
 L+=['  let '+n+' : Expr (Fin 36) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]
 L+=['  let '+n+' := '+str(a)+' '+o+' '+str(b) for n,o,a,b in g['source']];body='\n'.join(L)
 env={x:('leaf',x) for x in g['witnesses']+g['fixed_numerals']}
 def v(x):return ('constant',x) if type(x)==int else env[x]
 for n,o,a,b in g['source']:env[n]=(o,v(a),v(b))
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
 literal='import AdaptiveQM37Literal\n\n'+pre+f'namespace DiophantineConsistency.AdaptiveQM36Literal{suffix}Draft\nopen AdaptiveEquationSyntax2011\n\ndef literal (p : Fin 4 → ℤ) : Expr (Fin 36) :=\n'+body+'\n  '+g['output']+f'\n\nend DiophantineConsistency.AdaptiveQM36Literal{suffix}Draft\n'
 sumexpr=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(27))
 residual='import AdaptiveQM36Literal'+suffix+'\n\n'+pre+f'namespace DiophantineConsistency.AdaptiveQM36Residuals{suffix}Draft\nopen AdaptiveEquationSyntax2011\n\ndef residuals (p : Fin 4 → ℤ) : Fin 27 → Expr (Fin 36) :=\n'+body+'\n  !['+','.join(res)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 36) := '+sumexpr+f'\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = AdaptiveQM36Literal{suffix}Draft.literal p := by rfl\nend DiophantineConsistency.AdaptiveQM36Residuals{suffix}Draft\n#print axioms DiophantineConsistency.AdaptiveQM36Residuals{suffix}Draft.sum_eq_literal\n'
 for tag,data in [('Literal',literal),('Residuals',residual)]:
  path=P/f'AdaptiveQM36{tag}{suffix}.lean.src';path.write_text(data);outputs[path.name]=hashlib.sha256(data.encode()).hexdigest()
print(json.dumps({'scope':'source-only generated literals and exact sum DAGs; no Lean','residuals':len(res),'variables':36,'outputs':outputs},indent=2,sort_keys=True))
