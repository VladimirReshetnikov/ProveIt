import GRHArticle.ProgressionFree.NumberFieldIdeals.Density

/-!
# Uniform norm-ball bounds

The asymptotic count of all nonzero ideals supplies a single constant
valid at every nonnegative real cutoff, including cutoffs below one.
For multiples of any given ideal, the same constant is divided by its norm.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology Ideal NumberField
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem countUpTo_mono {A B : Set (Ideal (𝓞 K))⁰} (h : A ⊆ B) {X Y : ℝ} (hXY : X ≤ Y)
    (hY : 0 ≤ Y) : countUpTo A X ≤ countUpTo B Y := by
  let B' := {I : (Ideal (𝓞 K))⁰ | I ∈ B ∧ (absNorm I.val : ℝ) ≤ Y}
  have hf : B'.Finite := (finite_setOf_absNorm_le₀ (S := 𝓞 K) ⌊Y⌋₊).subset
    fun _ hI ↦ (Nat.le_floor_iff hY).mpr hI.2
  apply Set.ncard_le_ncard (t := B') _ hf
  exact fun _ hI ↦ ⟨h hI.1,hI.2.trans hXY⟩

theorem countUpTo_zero_of_lt_one (A : Set (Ideal (𝓞 K))⁰) {X : ℝ} (hX : X < 1) :
    countUpTo A X = 0 := by
  let B := {I : (Ideal (𝓞 K))⁰ | I ∈ A ∧ (absNorm I.val : ℝ) ≤ X}
  have h : B = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun I hI ↦ by
    have h1 : (1:ℝ) ≤ absNorm I.val := by exact_mod_cast absNorm_pos_of_nonZeroDivisors I
    exact (not_lt_of_ge (h1.trans hI.2)) hX
  change B.ncard = 0
  simp [h]

/-- In any number field the count of all nonzero ideals is bounded by
`C * X` for every nonnegative real `X`. -/
theorem exists_uniform_countUpTo_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 ≤ X →
      (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X : ℝ) ≤ C * X := by
  let r := dedekindZeta_residue K
  have hr : 0 < r := dedekindZeta_residue_pos K
  obtain ⟨U,hU⟩ := eventually_atTop.mp ((tendsto_countUpTo_univ_div (K := K)).eventually_lt_const
    (show dedekindZeta_residue K < r+1 by dsimp [r]; linarith))
  let T := max U 1
  let C := max (r+1) (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) T : ℝ)
  have hC : 0 < C := (show 0 < r+1 by linarith).trans_le (le_max_left _ _)
  refine ⟨C,hC,fun X hX ↦ ?_⟩
  by_cases h1 : X < 1
  · rw [countUpTo_zero_of_lt_one _ h1, Nat.cast_zero]
    exact mul_nonneg hC.le hX
  · have h1' := le_of_not_gt h1
    by_cases ht : T ≤ X
    · exact ((div_lt_iff₀ (zero_lt_one.trans_le h1')).mp
        (hU X ((le_max_left _ _).trans ht))).le.trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
    · have hc := Nat.cast_le (α := ℝ).mpr (countUpTo_mono (A := Set.univ) (B := Set.univ)
          (K := K) (Set.Subset.rfl) (le_of_not_ge ht) (zero_le_one.trans (le_max_right _ _)))
      exact (hc.trans (le_max_right _ _)).trans (le_mul_of_one_le_right hC.le h1')

/-- A bound uniform in both the ideal multiplier and the set being scaled. -/
theorem exists_uniform_mul_image_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : (Ideal (𝓞 K))⁰) (A : Set (Ideal (𝓞 K))⁰) (X : ℝ), 0 < X →
      (countUpTo ((J * ·) '' A) X : ℝ)/X ≤ C / absNorm J.val := by
  obtain ⟨C,hC,hcount⟩ := exists_uniform_countUpTo_bound (K := K)
  refine ⟨C,hC,fun J A X hX ↦ ?_⟩
  rw [countUpTo_mul_image, div_le_iff₀ hX]
  have hJ : (0:ℝ) < absNorm J.val := Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J)
  have ht := (div_pos hX hJ).le
  have hc := Nat.cast_le (α := ℝ).mpr (countUpTo_mono (Set.subset_univ A) le_rfl ht)
  exact (hc.trans (hcount _ ht)).trans_eq (by ring)

end GRHArticle.ProgressionFree.NumberFieldIdeals
