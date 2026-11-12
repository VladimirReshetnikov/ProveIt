import FirstQuotient88
import MainBalance87
import RingNormExtraction

/-! Source-only 88 own-zero main norm, without signed root orientation,
rank casts, mask bounds or a parent zero. No Lean elaboration is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MainNorm88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open MainBalance87Draft StrongNorm87Draft FirstFields86Draft AuxRingNormExtractionDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A signed scaled 88 own-zero main norm yields a natural square root;
no choice of the scaled root's sign is needed. -/
theorem main_norm (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hY : 0<v 7)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    ∃ d : V, d*d=1+Delta v*c v*c v := by
  let u := PositiveMap88To87Draft.forward v
  have hz' : InternalZero (P87ShiftedGuard.graph p).output u := FirstQuotient88Draft.forward_zero p v hz
  have hq : 0<q beta u := by dsimp [q]; simp
  have hY' : 0<Y u := by simpa [Y,u,PositiveMap88To87Draft.forward] using hY
  have hU : 0<U beta u := by dsimp [U]; exact mul_pos hY' (mul_pos hq hq)
  have hm := (FourFields87Draft.fields_of_zero p u hz').2.1
  rw [MainBalance87Draft.main_eval p beta u hport] at hm
  have hroot := root_of_scaled_ring_square (U beta u) (1+Delta u*c u*c u)
    (MainBalance87Draft.mainValue p beta u) hU (sub_eq_zero.mp hm)
  simpa [u,PositiveMap88To87Draft.forward,Delta,a,c,k] using hroot

end DiophantineConsistency.MainNorm88Draft

#print axioms DiophantineConsistency.MainNorm88Draft.main_norm
