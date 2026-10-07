import OAI.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem real_sub_grade_mem_sup_next (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ V ⊔ (F.realLayer j).toSubmodule) :
    x - basisGradeProjection (b.baseChange ℝ) w j x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have ht : basisBelowProjection (b.baseChange ℝ) w j z = 0 := by
    have hz' : z - 0 ∈ F.realification.layer j := by rw [sub_zero]; exact hz
    have h := (F.realGradeTruncation_eq_iff b w hlayers j z 0).mpr hz'
    simpa only [map_zero] using h
  have hhigh := F.sub_realGradeTruncation_mem b w hlayers (j + 1) z
  rw [basisBelowProjection_succ, ht, zero_add] at hhigh
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (Submodule.mem_sup_left (V.sub_mem hv (hV j v hv))) (Submodule.mem_sup_right hhigh)
  simpa only [map_add, add_sub_add_comm] using h

include hlayers in
theorem real_matching_grade_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ) (x y : ℝ ⊗[ℚ] L)
    (hx : x ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hmatch : basisGradeProjection (b.baseChange ℝ) w j x - y ∈ V) :
    x - y ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (F.real_sub_grade_mem_sup_next b w hlayers V hV j x hx) (Submodule.mem_sup_left hmatch)
  simpa only [sub_add_sub_cancel] using h

include hlayers in
theorem polynomial_lift_matching_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hX : ∀ α, coefficients X α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hmatch : ∀ α, coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X - Y) α ∈ V) :
    ∀ α, coefficients (X - Y) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro α
  rw [map_sub, Finsupp.sub_apply]
  apply F.real_matching_grade_remainder b w hlayers V hV j _ _ (hX α)
  have h := hmatch α
  simpa only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
