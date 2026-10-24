#!/usr/bin/env python3
import json
from pathlib import Path
R=Path(__file__).resolve().parent
obj=json.loads((R/'affine_shared_step.json').read_text());w=obj['witnesses'];ex=obj['exposed_coordinates'];n=len(w)
def atom(s):return f'(.var (.inl {ex.index(s)}))' if s in ex else f'(.var (.inr {w.index(s)}))'
def expr(rows):return ' + '.join('('+' * '.join([f'(.constant ({r["coefficient"]} : ℤ))']+[atom(s) for s in r['monomial']])+')' for r in rows) or '0'
old=(R/'AffineProductEquation.lean').read_text()
a=old.index('def stepPolynomial');b=old.index('def stepRep',a)
s=f'def stepPolynomial : Expr (Fin 4 ⊕ Fin {n}) :=\n'
for i,branch in enumerate(obj['horn_source']['branches']):s+=f'  let h{i} : Expr (Fin 4 ⊕ Fin {n}) := {expr(branch["sum_of_squares"])}\n'
for i,res in enumerate(obj['extra_residuals']):s+=f'  let e{i} : Expr (Fin 4 ⊕ Fin {n}) := {expr(res)}\n'
s+='  '+' * '.join(f'h{i}' for i in range(len(obj['horn_source']['branches'])))+' + '+' + '.join(f'e{i} * e{i}' for i in range(len(obj['extra_residuals'])))+'\n\n'
s=(old[:a]+s+old[b:]).replace('AffineProductProposal','SharedAffineProductProposal')
(R/'SharedAffineProductEquation.lean').write_text(s)
print('Emitted UNCOMPILED SharedAffineProductEquation.lean with',n,'local witnesses')
