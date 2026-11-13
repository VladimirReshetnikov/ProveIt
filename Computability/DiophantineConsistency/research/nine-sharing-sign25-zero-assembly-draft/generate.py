#!/usr/bin/env python3
"""Generate source-only indexed forward/backward zero assembly."""
from pathlib import Path
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent
common='''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
idx=[1,2,3,5,6,7,8,10,11,12,13,14,15,16]
def old(i):return 'Sign25FirstCut.oldEll' if i==4 else 'Sign25FirstCut.oldN0' if i==9 else f'Sign25RemainingCuts.oldR{i:02d}'
def new(i):return 'Sign25FirstCut.newN0' if i==9 else f'Sign25RemainingCuts.newR{i:02d}'
def evalname(i):return 'Sign25FirstCut.N0_eval' if i==9 else f'Sign25RemainingCuts.R{i:02d}_eval'
def row(i,side):return f'Sign25FirstCut.{side}_N0_row' if i==9 else f'Sign25RemainingCuts.{side}_R{i:02d}_row'
assert set(idx)==set(range(1,17))-{4,9}
oldlist=['SharingSeed26Sextic.firstResidual']+[old(i) for i in range(1,17)];newidx=[i for i in range(1,17) if i!=4];newlist=['SharingSeed25Octic.firstResidual']+[new(i) for i in newidx]
f='''import DiophantineConsistency.Sign25CoordinateDrop

/-! SOURCE-ONLY forward zero assembly. -/
'''+common+'''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed26Sextic.firstResidual p :: SharingSeed26Sextic.remainingResiduals p =
      ['''+',\n       '.join(x+' p' for x in oldlist)+'''] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 26 → V)
    (hz : InternalZero (SharingSeed25Octic.seed p) v) :
    InternalZero (SharingSeed26Sextic.seed p) (Sign25FirstCut.lift v) := by
  have hn := (SharingSign25Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign26Squares.seed_zero_iff_residuals p (Sign25FirstCut.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with '''+' | '.join('rfl' for _ in oldlist)+'''
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.first_eval p v)).mpr (hn _ List.mem_cons_self)
'''
for i in range(1,17):
 if i==4:f+='  · exact Sign25FirstCut.old_ell_zero p v\n'
 else:f+=f'  · exact (zero_iff_of_eval_eq _ _ _ _ ({evalname(i)} p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? ({row(i,"new")} p)))))\n'
f+='end DiophantineConsistency.Sign25ZeroBridge\n#print axioms DiophantineConsistency.Sign25ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign25ZeroBridge.forward\n'
r='''import DiophantineConsistency.Sign25ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
'''+common+'''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed25Octic.firstResidual p :: SharingSeed25Octic.remainingResiduals p =
      ['''+',\n       '.join(x+' p' for x in newlist)+'''] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 27 → V)
    (hz : InternalZero (SharingSeed26Sextic.seed p) v) :
    InternalZero (SharingSeed25Octic.seed p) (Sign25CoordinateRecover.drop v) := by
  have hz' : InternalZero (SharingSeed26Sextic.seed p)
      (Sign25FirstCut.lift (Sign25CoordinateRecover.drop v)) := by
    rw [Sign25CoordinateRecover.lift_drop p v hz]
    exact hz
  have ho := (SharingSign26Squares.seed_zero_iff_residuals p
    (Sign25FirstCut.lift (Sign25CoordinateRecover.drop v))).mp hz'
  apply (SharingSign25Squares.seed_zero_iff_residuals p (Sign25CoordinateRecover.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with '''+' | '.join('rfl' for _ in newlist)+'''
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.first_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ List.mem_cons_self)
'''
for i in newidx:r+=f'  · exact (zero_iff_of_eval_eq _ _ _ _ ({evalname(i)} p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? ({row(i,"old")} p)))))\n'
r+='end DiophantineConsistency.Sign25ZeroBridge\n#print axioms DiophantineConsistency.Sign25ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign25ZeroBridge.backward\n'
for n,s in [('Sign25ForwardBridge.lean',f),('Sign25ReverseBridge.lean',r)]:
 q=p/n;assert not q.exists();q.write_text(s)
print('GENERATED_SOURCE_ONLY old 17/new 16 rows; Lean untested')
