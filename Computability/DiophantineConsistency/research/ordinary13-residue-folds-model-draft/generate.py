#!/usr/bin/env python3
"""Reconstruct four inert graph literals and residual vectors; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
spec=[('P89','ordinary13-natural-residue-forced89-degree56','c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a',89),('Fold88','ordinary13-natural-residue-eta-fold88-degree56','f71cb18bdc28088a7a7c7c7ae84afc15e49470ee3d4fa4076d8c25d6d2b89b58',88),('P88','ordinary13-natural-residue-forced88-degree60','cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2',88),('Fold87','ordinary13-natural-residue-eta-fold87-degree60','81a09c0504bc786afb017483225e1fb6b1a52e9ddd98f53b0643dfb23c3a602f',87)]
pre='''/-! Generated inert graph source; no Lean elaboration. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
'''
outs={}
for tag,path,want,count in spec:
 raw=(D/'research'/path/'candidate.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==want;g=json.loads(raw)
 assert len(g['witnesses'])==13 and len(g['source'])==g['operations']==count
 names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']];assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in names)
 body='\n'.join(['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(g['witnesses'])]+['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]+['  let '+n+' := '+str(a)+' '+o+' '+str(b) for n,o,a,b in g['source']])
 env={x:('leaf',x) for x in g['witnesses']+g['fixed_numerals']}
 for n,o,a,b in g['source']:
  get=lambda x: ('constant',x) if type(x)==int else env[x]
  env[n]=(o,get(a),get(b))
 r=['A0','A1','Fam','g72'];q=[('*',env[x],env[x]) for x in r];assert env[g['output']]==('+',('+',q[0],q[1]),('+',q[2],q[3]))
 ns='DiophantineConsistency.ResidueFold'+tag+'Draft'
 lit='import DiophantineConsistency.AdaptiveEquationSyntax2011\n\n'+pre+'namespace '+ns+'\nopen AdaptiveEquationSyntax2011\n\ndef literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n'+body+'\n  '+g['output']+'\n\nend '+ns+'\n'
 rs='import ResidueFold'+tag+'\n\n'+pre+'namespace '+ns+'Residuals\nopen AdaptiveEquationSyntax2011\n\ndef residuals (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 13) :=\n'+body+'\n  !['+','.join(r)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n  ((residuals p 0)*(residuals p 0)+(residuals p 1)*(residuals p 1))+((residuals p 2)*(residuals p 2)+(residuals p 3)*(residuals p 3))\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = '+ns+'.literal p := by rfl\nend '+ns+'Residuals\n'
 assert ': Fin 4 → Expr (Fin 13)' in rs and len(r)==4
 for f,s in [('ResidueFold'+tag+'.lean.src',lit),('ResidueFold'+tag+'Residuals.lean.src',rs)]:
  if '--initialize' in sys.argv:(P/f).write_text(s)
  else:assert (P/f).read_text()==s
  outs[f]=hashlib.sha256(s.encode()).hexdigest()
print(json.dumps({'scope':'graph source/DAG reconstruction, no Lean','files':outs,'operations':[89,88,88,87],'residual_arity':4},sort_keys=True,indent=2))
