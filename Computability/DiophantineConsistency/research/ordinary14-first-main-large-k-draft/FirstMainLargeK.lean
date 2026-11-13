import MainSquareGap
import AuxRootBounds

/-! Source-only model fact from natural first/main norms; no literal graph,
strong norm, root sign, parent witness or Lean elaboration is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstMainLargeKDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelMainSquareGapDraft AuxRootBoundsModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first/main norms and positive scalar parameters force k≥8XY²+4.
This is the standalone part of the existing norms-to-aux-bounds draft. -/
theorem first_main_large_k (X Y eta zeta tau d Delta : V)
    (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)
    (hDelta : (X*Y+Y+2)*(X*Y+Y+2)=Delta+1)
    (hfirst : tau*tau=1+(X*Y*Y)*(X*Y*Y+1)*(eta+zeta)*(eta+zeta))
    (hmain : d*d=1+Delta*(eta+Y*(eta+zeta))*(eta+Y*(eta+zeta))) :
    8*X*Y*Y+4≤eta+zeta := by
  have hkne : eta+zeta≠2 :=
    two_ordinate_impossible X Y eta zeta Delta d hX hY heta hzeta hDelta hmain
  have hkge : (2:V)≤eta+zeta := by
    have h := add_le_add (pos_iff_one_le.mp heta) (pos_iff_one_le.mp hzeta)
    simpa only [show (1:V)+1=2 by ring] using h
  have hkgt : 2<eta+zeta := lt_of_le_of_ne hkge (Ne.symm hkne)
  have hm : 0<X*Y*Y := mul_pos (mul_pos hX hY) hY
  have h := first_ordinate_large (X*Y*Y) tau (eta+zeta) hm hkgt hfirst
  simpa only [show 8*(X*Y*Y)=8*X*Y*Y by ring] using h

end DiophantineConsistency.FirstMainLargeKDraft

#print axioms DiophantineConsistency.FirstMainLargeKDraft.first_main_large_k
