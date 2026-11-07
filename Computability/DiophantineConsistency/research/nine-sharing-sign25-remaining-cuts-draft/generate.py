#!/usr/bin/env python3
"""Generate source-only unchanged-row transfer clients from pinned Lean syntax."""
import hashlib,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent;d=p.parents[1];h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();old=d/'research/nine-sharing-sign26-sextic-lean-draft/SharingSeed26Sextic.lean';new=d/'research/nine-sharing-sign25-octic-lean-draft/SharingSeed25Octic.lean'
assert h(old)=='f2614a350eb1b6777bf9acc5723824ddb9362cebd23da6f80ae9e8c5860e5751' and h(new)=='25f4c55e4f9587db295d4fe95908ef6866202c9690204b9dfa88c27b7ea547ec'
def rows(path,n):
 s=path.read_text();first=s.split(f'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin {n}) :=\n  ',1)[1].split('\n',1)[0];block=s.split(f'def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin {n})) :=\n  [\n',1)[1].split('\n  ]',1)[0];return [first]+[x.strip().removesuffix(',') for x in block.splitlines()]
a,b=rows(old,27),rows(new,26);assert len(a)==17 and len(b)==16
idx=[1,2,3,5,6,7,8,10,11,12,13,14,15,16]
for stage,group in enumerate((idx[:7],idx[7:])):
 name=f'Sign25RemainingCuts{stage:02d}';out=p/(name+'.lean');assert not out.exists()
 s='import DiophantineConsistency.'+('Sign25FirstCut' if stage==0 else 'Sign25RemainingCuts00')+'''\n\n/-! SOURCE-ONLY: unchanged residual transfers; no zero bridge. -/\nset_option autoImplicit false\nnoncomputable section\nnamespace DiophantineConsistency.Sign25RemainingCuts\nopen LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing\nopen scoped LO.FirstOrder LO.FirstOrder.Arithmetic\nopen AdaptiveEquationSyntax2011\nvariable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]\n'''
 if stage==0:
  s+='''\ntheorem first_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (SharingSeed26Sextic.firstResidual p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (SharingSeed25Octic.firstResidual p).evalRing (fun j => ι (v j)) := by
  simp [SharingSeed26Sextic.firstResidual, SharingSeed25Octic.firstResidual,
    Sign25FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant]
'''
 for i in group:
  j=i if i<4 else i-1;assert '(Expr.var 19)' not in a[i],i
  s+=f'''\ndef oldR{i:02d} (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  {a[i]}
def newR{i:02d} (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  {b[j]}
theorem old_R{i:02d}_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop {i-1}).head? = some (oldR{i:02d} p) := by rfl
theorem new_R{i:02d}_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop {j-1}).head? = some (newR{i:02d} p) := by rfl
theorem R{i:02d}_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR{i:02d} p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR{i:02d} p).evalRing (fun j => ι (v j)) := by
  simp [oldR{i:02d}, newR{i:02d}, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]
'''
 s+='end DiophantineConsistency.Sign25RemainingCuts\n'
 if stage==0:s+='#print axioms DiophantineConsistency.Sign25RemainingCuts.first_eval\n'
 for i in group:
  for x in (f'old_R{i:02d}_row',f'new_R{i:02d}_row',f'R{i:02d}_eval'):s+=f'#print axioms DiophantineConsistency.Sign25RemainingCuts.{x}\n'
 out.write_text(s)
print('GENERATED_SOURCE_ONLY 14 rows and first residual; no Lean theorem claim')
