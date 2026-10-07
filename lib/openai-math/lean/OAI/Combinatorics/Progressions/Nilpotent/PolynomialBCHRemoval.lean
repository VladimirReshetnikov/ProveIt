import OAI.Combinatorics.Progressions.Estimates.CurrentLayerPreservation

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def bchRemove (s : ℕ) (A P B : VectorPolynomial σ ℚ L) :
    VectorPolynomial σ ℚ L := lieBCH s (lieBCH s (-A) P) (-B)

theorem bchRemove_factorization {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (A P B : VectorPolynomial σ ℚ L) :
    lieBCH s (lieBCH s A (bchRemove s A P B)) B = P := by
  let a : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨A⟩
  let g : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨P⟩
  let c : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨B⟩
  have h : a * (a⁻¹ * g * c⁻¹) * c = g := by group
  exact congrArg NilpotentLieBCHGroup.coord h

theorem eval₂_bchRemove [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (s : ℕ) (A P B : VectorPolynomial σ ℚ L) (t : σ → ℝ) :
    eval₂ t (bchRemove s A P B) = lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B) := by
  have h₁ := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) s (lieBCH s (-A) P) (-B)
  have h₂ := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) s (-A) P
  rw [h₂] at h₁
  simp only [map_neg, eval₂Lie_apply] at h₁
  exact h₁

theorem bchRemove_constant {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (A P B : VectorPolynomial σ ℚ L) (hA : coefficients A 0 = 0) (hB : coefficients B 0 = 0) :
    coefficients (bchRemove s A P B) 0 = coefficients P 0 := by
  have h₁ := eval_lieBCH (fun _ : σ => (0 : ℚ)) s (lieBCH s (-A) P) (-B)
  have h₂ := eval_lieBCH (fun _ : σ => (0 : ℚ)) s (-A) P
  rw [h₂] at h₁
  simp only [map_neg, eval_zero_eq_coefficient, hA, hB, neg_zero] at h₁
  apply h₁.trans
  change ((1 : NilpotentLieBCHGroup L s hnil) * ⟨coefficients P 0⟩ * 1).coord = _
  simp only [one_mul, mul_one]

theorem bchRemove_coefficients_mem (U : LieSubalgebra ℚ L) (s : ℕ)
    (A P B : VectorPolynomial σ ℚ L)
    (hA : ∀ α, coefficients A α ∈ U) (hP : ∀ α, coefficients P α ∈ U)
    (hB : ∀ α, coefficients B α ∈ U) :
    ∀ α, coefficients (bchRemove s A P B) α ∈ U := by
  let W := coefficientLieSubalgebra (σ := σ) U
  have ha : A ∈ W := hA
  have hp : P ∈ W := hP
  have hb : B ∈ W := hB
  exact lieBCH_mem W s (lieBCH_mem W s (W.neg_mem ha) hp) (W.neg_mem hb)

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem polynomial_bchRemove_grades (E : Submodule ℝ (ℝ ⊗[ℚ] L)) (j : ℕ)
    (hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (A P B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E) (hB : ∀ α, coefficients B α ∈ E) :
    map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (bchRemove s A P B) =
      map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P - A - B ∧
      ∀ d < j, map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) (bchRemove s A P B) =
        map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P := by
  have heq (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
      (h : ∀ t : σ → ℝ, eval₂ t X = eval₂ t Y) : X = Y := by
    apply sub_eq_zero.mp
    apply eq_zero_of_eval₂_zero (K := ℝ)
    intro t
    rw [map_sub, h t, sub_self]
  have hvalues (t : σ → ℝ) :
      basisGradeProjection (b.baseChange ℝ) w j
          (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) =
        basisGradeProjection (b.baseChange ℝ) w j (eval₂ t P) - eval₂ t A - eval₂ t B ∧
      ∀ d < j, basisGradeProjection (b.baseChange ℝ) w d
          (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) =
        basisGradeProjection (b.baseChange ℝ) w d (eval₂ t P) := by
    have ha := hE _ ((eval₂_mem_iff_coefficients E A).mpr hA t)
    have hc := hE _ ((eval₂_mem_iff_coefficients E B).mpr hB t)
    have hal : eval₂ t A ∈ F.realification.layer j := by
      simpa only [ha] using F.realGradeProjection_mem_layer b w hlayers j (eval₂ t A)
    have hcl : eval₂ t B ∈ F.realification.layer j := by
      simpa only [hc] using F.realGradeProjection_mem_layer b w hlayers j (eval₂ t B)
    have hcurrent := F.real_correction_current_grade b w hlayers j
      ⟨eval₂ t A⟩ ⟨eval₂ t P⟩ ⟨eval₂ t B⟩ hal hcl
    have hbelow := F.real_correction_preserves_grades_below b w hlayers j
      ⟨eval₂ t A⟩ ⟨eval₂ t P⟩ ⟨eval₂ t B⟩ hal hcl
    change basisGradeProjection (b.baseChange ℝ) w j
      (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) = _ at hcurrent
    rw [ha, hc] at hcurrent
    exact ⟨hcurrent, hbelow⟩
  constructor
  · apply heq
    intro t
    simp only [eval₂_map, eval₂_bchRemove, map_sub]
    exact (hvalues t).1
  · intro d hd
    apply heq
    intro t
    simp only [eval₂_map, eval₂_bchRemove]
    exact (hvalues t).2 d hd

end NilpotentLieFiltration
end Erdos3

end

end OAI
