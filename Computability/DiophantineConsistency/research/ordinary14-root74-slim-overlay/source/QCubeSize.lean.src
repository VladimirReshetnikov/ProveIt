import GraphNormClient

/-! Source-only model size bound for the 84/79 q-cubed ordinate. No graph
zero, port identification, compilation or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.QCubeSize84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive beta, J and s force q≥2 and Y=q³s≥8 in the model. -/
theorem Y_at_least_eight (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hs : 0<v 7) :
    8≤AuxGraphNormClientDraft.Y beta v := by
  let q := AuxGraphNormClientDraft.q beta v
  have hprod : 0<v 0*beta := mul_pos hJ hbeta
  have hp1 : 1≤v 0*beta := pos_iff_one_le.mp hprod
  have hq : 2≤q := by dsimp [q,AuxGraphNormClientDraft.q]; nlinarith
  have hq2 : 4≤q*q := by
    have h := mul_le_mul hq hq (by norm_num : (0:V)≤2) (Arithmetic.zero_le q)
    norm_num at h ⊢
    exact h
  have hq3 : 8≤q*(q*q) := by
    have h := mul_le_mul hq hq2 (by norm_num : (0:V)≤4) (Arithmetic.zero_le q)
    norm_num at h ⊢
    exact h
  have hs1 : 1≤v 7 := pos_iff_one_le.mp hs
  calc
    (8:V)≤q*(q*q) := hq3
    _≤(q*(q*q))*v 7 := le_mul_of_one_le_right (Arithmetic.zero_le _) hs1
    _=AuxGraphNormClientDraft.Y beta v := by rfl

end DiophantineConsistency.QCubeSize84Draft

#print axioms DiophantineConsistency.QCubeSize84Draft.Y_at_least_eight
