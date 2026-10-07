import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

namespace Erdos3

theorem overlap_weight_comparison (j : ℕ) {q r C D c δ : ℝ}
    (hq : 0 < q) (hr : 0 ≤ r) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hD : 0 < D) (hDq : D ≤ q ^ (j + 3))
    (hC : c * r ^ (j + 2) ≤ C) (hδr : δ * q ≤ r) :
    c * δ ^ (j + 1) * (r / q ^ 2) ≤ C / D := by
  have hδq : δ ≤ r / q := (le_div_iff₀ hq).mpr hδr
  have hC0 : 0 ≤ C := (mul_nonneg hc (pow_nonneg hr _)).trans hC
  calc
    _ ≤ c * (r / q) ^ (j + 1) * (r / q ^ 2) := by gcongr
    _ = (c * r ^ (j + 2)) / q ^ (j + 3) := by
      simp only [div_pow, pow_succ]
      field_simp
    _ ≤ C / q ^ (j + 3) := div_le_div_of_nonneg_right hC (by positivity)
    _ ≤ C / D := div_le_div_of_nonneg_left hC0 hD hDq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem box_overlap_cube_weight (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)]
    (j : ℕ) {h : ι → ℤ} (hh : h ∈ cubeDifferenceSupport (translatedIntegerBox a T))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsize : δ * (translatedIntegerBox a T).card ≤
      ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ)) :
    let Q := translatedIntegerBox a T
    let R := derivativeSupport Q h
    ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι * δ ^ (j + 1) *
        ((R.card : ℝ) / (Q.card : ℝ) ^ 2) ≤
      (Nat.card (SupportedCube (j + 1) (R : Set (ι → ℤ))) : ℝ) /
        Nat.card (SupportedCube (j + 2) (Q : Set (ι → ℤ))) := by
  let Q := translatedIntegerBox a T
  let lengths := fun i => ((T i : ℤ) - |h i|).toNat
  let origin := fun i => a i + max 0 (-h i)
  let : ∀ i, NeZero (lengths i) := fun i => ⟨(box_overlap_length_pos a T hh i).ne'⟩
  have hR : derivativeSupport Q h = translatedIntegerBox origin lengths :=
    derivativeSupport_translatedIntegerBox a T h
  have hC := (translatedIntegerBox_cubeCount_bounds lengths origin (j + 1)).1
  rw [← hR] at hC
  have hC' : ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι *
      ((derivativeSupport Q h).card : ℝ) ^ (j + 2) ≤
      Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set (ι → ℤ))) := by
    convert hC using 1
    push_cast
    ring
  apply overlap_weight_comparison j
    (by exact_mod_cast (translatedIntegerBox_nonempty T a).card_pos)
    (Nat.cast_nonneg _) (by positivity) hδ
    (by exact_mod_cast card_supportedCube_pos (j + 2) (translatedIntegerBox_nonempty T a))
    _ hC' hsize
  exact_mod_cast card_supportedCube_le (j + 2) Q

end Erdos3

end

end OAI
