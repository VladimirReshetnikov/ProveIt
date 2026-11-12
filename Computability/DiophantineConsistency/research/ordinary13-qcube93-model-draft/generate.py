#!/usr/bin/env python3
"""Read-only reconstruction of parent/child inert syntax; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
spec=[('Parent','research/ordinary13-natural-cfold-forced-x95-degree28/candidate.json','5fd11fa456867a2ed4f3b5bc58db59caab0f58736019ee864403d62124aced4e',95),('Child','research/ordinary13-natural-qcube-quotient93-degree56/candidate.json','346a4895448a2212ce2617ef805fd3ea164d7d8896d5bad2c210cf19cd3ef21a',93)]
pre='''/-! Generated inert graph source; no Lean elaboration. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
'''
outs={}
for tag,path,want,count in spec:
 raw=(D/path).read_bytes();assert hashlib.sha256(raw).hexdigest()==want;g=json.loads(raw)
 assert len(g['witnesses'])==13 and len(g['source'])==g['operations']==count
 names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']]
 assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in names)
 body='\n'.join(['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(g['witnesses'])]+['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]+['  let '+n+' := '+str(a)+' '+o+' '+str(b) for n,o,a,b in g['source']])
 env={x:('leaf',x) for x in g['witnesses']+g['fixed_numerals']}
 for n,o,a,b in g['source']:
  get=lambda x: ('constant',x) if type(x)==int else env[x]
  env[n]=(o,get(a),get(b))
 r=['A0','A1','Fam','g72'];q=[('*',env[x],env[x]) for x in r]
 assert env[g['output']]==('+',('+',q[0],q[1]),('+',q[2],q[3]))
 namespace='DiophantineConsistency.Ordinary13QCube93'+tag+'Draft'
 lit='import DiophantineConsistency.AdaptiveEquationSyntax2011\n\n'+pre+'namespace '+namespace+'\nopen AdaptiveEquationSyntax2011\n\ndef literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n'+body+'\n  '+g['output']+'\n\nend '+namespace+'\n'
 residual='import Ordinary13QCube93'+tag+'\n\n'+pre+'namespace '+namespace+'Residuals\nopen AdaptiveEquationSyntax2011\n\ndef residuals (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 13) :=\n'+body+'\n  !['+','.join(r)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n  ((residuals p 0)*(residuals p 0)+(residuals p 1)*(residuals p 1))+((residuals p 2)*(residuals p 2)+(residuals p 3)*(residuals p 3))\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = '+namespace+'.literal p := by rfl\nend '+namespace+'Residuals\n'
 assert ': Fin 4 → Expr (Fin 13)' in residual and len(r)==4
 for filename,s in [('Ordinary13QCube93'+tag+'.lean.src',lit),('Ordinary13QCube93'+tag+'Residuals.lean.src',residual)]:
  if '--initialize' in sys.argv:(P/filename).write_text(s)
  else:assert (P/filename).read_text()==s
  outs[filename]=hashlib.sha256(s.encode()).hexdigest()
print(json.dumps({'scope':'source syntax reconstruction only; no Lean','files':outs,'row_counts':[95,93],'residuals_each':4,'sum_syntax_checked':True},sort_keys=True,indent=2))
