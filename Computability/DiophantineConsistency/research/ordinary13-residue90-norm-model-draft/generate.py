#!/usr/bin/env python3
"""Reconstruct the 90-row graph and its four residuals; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
b=(D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946';g=json.loads(b)
assert len(g['witnesses'])==13 and len(g['source'])==g['operations']==90
names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']];assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in names)
body='\n'.join(['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(g['witnesses'])]+['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]+['  let '+n+' := '+str(a)+' '+o+' '+str(b) for n,o,a,b in g['source']])
env={x:('leaf',x) for x in g['witnesses']+g['fixed_numerals']}
for n,o,a,b in g['source']:
 get=lambda x: ('constant',x) if type(x)==int else env[x]
 env[n]=(o,get(a),get(b))
r=['A0','A1','Fam','g72'];q=[('*',env[x],env[x]) for x in r]
assert env[g['output']]==('+',('+',q[0],q[1]),('+',q[2],q[3]))
pre='''/-! Generated inert graph source; no Lean elaboration. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
'''
ns='DiophantineConsistency.Residue90LiteralDraft'
lit='import DiophantineConsistency.AdaptiveEquationSyntax2011\n\n'+pre+'namespace '+ns+'\nopen AdaptiveEquationSyntax2011\n\ndef literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n'+body+'\n  '+g['output']+'\n\nend '+ns+'\n'
rs='import Residue90Literal\n\n'+pre+'namespace DiophantineConsistency.Residue90ResidualsDraft\nopen AdaptiveEquationSyntax2011\n\ndef residuals (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 13) :=\n'+body+'\n  !['+','.join(r)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n  ((residuals p 0)*(residuals p 0)+(residuals p 1)*(residuals p 1))+((residuals p 2)*(residuals p 2)+(residuals p 3)*(residuals p 3))\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = Residue90LiteralDraft.literal p := by rfl\nend DiophantineConsistency.Residue90ResidualsDraft\n'
assert ': Fin 4 → Expr (Fin 13)' in rs and len(r)==4
outs={}
for f,s in [('Residue90Literal.lean.src',lit),('Residue90Residuals.lean.src',rs)]:
 if '--initialize' in sys.argv:(P/f).write_text(s)
 else:assert (P/f).read_text()==s
 outs[f]=hashlib.sha256(s.encode()).hexdigest()
print(json.dumps({'scope':'exact graph syntax reconstruction; no Lean','files':outs,'operations':90,'variables':13,'residual_arity':4,'sum_syntax_checked':True},sort_keys=True,indent=2))
