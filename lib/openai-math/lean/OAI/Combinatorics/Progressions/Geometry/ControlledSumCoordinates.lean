import Mathlib.Data.Matrix.ColumnRowPartitioned
import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
import OAI.Combinatorics.Progressions.Linear.SortedBasisTriangular

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem real_column_span_fromCols {ι κ ν : Type*}
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) :
    Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col) =
      Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
        Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) := by
  rw [Matrix.fromCols_map]
  have hr : Set.range (Matrix.fromCols (A.map (Rat.castHom ℝ)) (B.map (Rat.castHom ℝ))).col =
      Set.range (A.map (Rat.castHom ℝ)).col ∪ Set.range (B.map (Rat.castHom ℝ)).col := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr j => exact Or.inr ⟨j, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  rw [hr, Submodule.span_union]

theorem exists_rational_sum_coordinates {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ S : Matrix (κ ⊕ ν) ι ℚ,
      (∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H)) ∧
      ∀ x, x ∈ Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
        Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) →
        A.map (Rat.castHom ℝ) *ᵥ ((S.map (Rat.castHom ℝ) *ᵥ x) ∘ Sum.inl) +
          B.map (Rat.castHom ℝ) *ᵥ ((S.map (Rat.castHom ℝ) *ᵥ x) ∘ Sum.inr) = x := by
  let C := Matrix.fromCols A B
  have hC : ∀ i j, RationalHeightLE (C i j) H := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section C hH hC
  refine ⟨S, hSH, fun x hx => ?_⟩
  have hx' : x ∈ LinearMap.range (C.map (Rat.castHom ℝ)).mulVecLin := by
    apply (real_column_span_mem_iff C x).mp
    change x ∈ Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col)
    rw [real_column_span_fromCols]
    exact hx
  have he := real_matrix_image_section_apply C S hS x hx'
  change C.map (Rat.castHom ℝ) *ᵥ (S.map (Rat.castHom ℝ) *ᵥ x) = x at he
  dsimp only [C] at he
  rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem pi_norm_restriction_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (f : κ → ι) : ‖x ∘ f‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact norm_le_pi_norm x (f i)

theorem exists_controlled_sum_coordinates {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ u : (ι → ℝ) →ₗ[ℝ] (κ → ℝ), ∃ v : (ι → ℝ) →ₗ[ℝ] (ν → ℝ),
        (∀ x, x ∈ Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
          Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) →
          A.map (Rat.castHom ℝ) *ᵥ u x + B.map (Rat.castHom ℝ) *ᵥ v x = x) ∧
        (∀ x, ‖u x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖ ∧
          ‖v x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖) ∧
        ∀ x, x ∈ realDenominatorGrid l →
          u x ∈ realDenominatorGrid m ∧ v x ∈ realDenominatorGrid m := by
  classical
  obtain ⟨S, hS, hdecomp⟩ := exists_rational_sum_coordinates A B hH hA hB
  let m := matrixDenominator S * l
  let u : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Sum.inl).comp (S.map (Rat.castHom ℝ)).mulVecLin
  let v : (ι → ℝ) →ₗ[ℝ] (ν → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Sum.inr).comp (S.map (Rat.castHom ℝ)).mulVecLin
  have hnorm (x : ι → ℝ) := real_image_section_norm_bound S H hS hp hι hcols hHp x
  have hgrid (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) := real_matrix_denominator_grid S l x hx
  refine ⟨m, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hS hp hι hcols hHp hlp, u, v, hdecomp, ?_, ?_⟩
  · intro x
    exact ⟨(pi_norm_restriction_le (S.map (Rat.castHom ℝ) *ᵥ x) Sum.inl).trans (hnorm x),
      (pi_norm_restriction_le (S.map (Rat.castHom ℝ) *ᵥ x) Sum.inr).trans (hnorm x)⟩
  · intro x hx
    exact ⟨realDenominatorGrid_comp m _ (hgrid x hx) Sum.inl,
      realDenominatorGrid_comp m _ (hgrid x hx) Sum.inr⟩

end Erdos3

end

end OAI
