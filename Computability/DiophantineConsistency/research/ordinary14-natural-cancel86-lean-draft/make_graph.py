#!/usr/bin/env python3
"""Render the reviewed natural 86 SLP as Expr rows; never invokes Lean."""
from pathlib import Path
import hashlib,json,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
candidate=D/'research/ordinary14-root74-natural-cancel86/candidate.json';raw=candidate.read_bytes();assert hashlib.sha256(raw).hexdigest()=='0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170';g=json.loads(raw)
inputs=['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_zeta','n_y','n_gamma','n_h'];ports=['beta','K0','MC','MF']
assert g['witnesses']==inputs and g['fixed_numerals']==ports and g['operations']==len(g['source'])==86 and g['output']=='out'
fields=[('first','F0'),('main','F1'),('aux','Fa'),('strong','Fs'),('guardFactor','guard'),('output','out'),('qF','qF'),('C','C'),('G','G'),('rank','R')]
head='''import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Literal source-only proposal. No Lean elaboration or endpoint claim. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P86NaturalCancel
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
'''+''.join('  '+n+' : Expr (Fin 14)\n' for n,_ in fields)+'''
set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
'''
lines=[f'  let {n} : Expr (Fin 14) := .var {i}' for i,n in enumerate(inputs)]
lines += [f'  let {n} : Expr (Fin 14) := .constant (p {i})' for i,n in enumerate(ports)]
lines+=['  -- BEGIN LITERAL GRAPH'];known=set(inputs+ports)
for n,op,x,y in g['source']:
 assert n not in known and op in ('+','-','*') and all(type(a) is int or a in known for a in (x,y))
 lines.append(f'  let {n} := {x} {op} {y}');known.add(n)
assert all(x in known for _,x in fields)
lines+=['  -- END LITERAL GRAPH','  ⟨'+', '.join(x for _,x in fields)+'⟩']
tail='''

theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).first * (graph p).main * (graph p).aux *
      (graph p).strong * (graph p).guardFactor - 1 := by rfl

end P86NaturalCancel

#print axioms P86NaturalCancel.output_shape
'''
data=(head+'\n'.join(lines)+tail).encode();out=P/'P86NaturalCancel.lean'
assert sys.argv[1:] in ([],['--check'])
if sys.argv[1:]==['--check']:assert out.read_bytes()==data
else:assert not out.exists();out.write_bytes(data)
print(json.dumps({'scope':'literal source generation only; no Lean or file binding','candidate_sha256':hashlib.sha256(raw).hexdigest(),'literal_sha256':hashlib.sha256(data).hexdigest(),'inputs':inputs,'ports':ports,'rows':86,'fields':dict(fields)},sort_keys=True,indent=2))
