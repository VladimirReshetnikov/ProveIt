import FirstQuotient88
import MainNorm88
import FirstMainLargeK
import FirstRootGap

/-! Source-only 88 own-zero first root gap, no parent root or Lean
elaboration. The separate model norm/descent clients are also drafts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstRootGap88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing FirstFields86Draft StrongNorm87Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 88 own zero supplies a positive q³ quotient and a first root above
m*k+s. No sign or parent zero is assumed. -/
theorem quotient_and_root_gap (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hX : 0<v 6) (hY : 0<v 7)
    (heta : 0<v 9) (hzeta : 0<v 10) (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    let m := (v 6*v 7)*v 7
    ∃ s tau : V, 0<s ∧ v 7=Q beta v*s ∧ 0<tau ∧ tau*tau=radicand v ∧
      8*m+4≤k v ∧ m*k v+s<tau := by
  let m := (v 6*v 7)*v 7
  obtain ⟨s,tau,hs,hYs,ht,hn⟩ := FirstQuotient88Draft.quotient_and_root p beta v hbeta hJ hY hport hz
  obtain ⟨d,hd⟩ := MainNorm88Draft.main_norm p beta v hbeta hJ hY hport hz
  have hDelta : (v 6*v 7+v 7+2)*(v 6*v 7+v 7+2)=Delta v+1 := by dsimp [Delta,a]; ring
  have hfirst : tau*tau=1+(v 6*v 7*v 7)*(v 6*v 7*v 7+1)*(v 9+v 10)*(v 9+v 10) := by
    rw [hn]
    dsimp [radicand,firstP,ell,k]
    ring
  have hmain : d*d=1+Delta v*(v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10)) := by
    simpa only [c,k] using hd
  have hk : 8*m+4≤k v := by
    simpa only [m,k] using FirstMainLargeKDraft.first_main_large_k
      (v 6) (v 7) (v 9) (v 10) tau d (Delta v) hX hY heta hzeta hDelta hfirst hmain
  have hq : 0<q beta v := by dsimp [q]; simp
  have hq1 : 1≤q beta v := pos_iff_one_le.mp hq
  have hQ1 : 1≤Q beta v := by
    dsimp [Q]
    exact one_le_mul_of_one_le_of_one_le hq1 (one_le_mul_of_one_le_of_one_le hq1 hq1)
  have hsY : s≤v 7 := by
    rw [hYs]
    exact le_mul_of_one_le_left (Arithmetic.zero_le s) hQ1
  have hX1 : 1≤v 6 := pos_iff_one_le.mp hX
  have hY1 : 1≤v 7 := pos_iff_one_le.mp hY
  have hYm : v 7≤m := calc
    v 7≤v 6*v 7 := le_mul_of_one_le_left (Arithmetic.zero_le (v 7)) hX1
    _≤(v 6*v 7)*v 7 := le_mul_of_one_le_right (Arithmetic.zero_le _) hY1
  have hsm : s≤m := le_trans hsY hYm
  have hm : 0<m := by dsimp [m]; exact mul_pos (mul_pos hX hY) hY
  have hgap := FirstRootGapDraft.root_gt_linear m (k v) tau s hm hsm hk (by simpa only [m] using hfirst)
  exact ⟨s,tau,hs,hYs,ht,hn,hk,hgap⟩

end DiophantineConsistency.FirstRootGap88Draft

#print axioms DiophantineConsistency.FirstRootGap88Draft.quotient_and_root_gap
