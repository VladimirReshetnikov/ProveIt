import GRHArticle.ProgressionFree.IntegerBoundaryPatch

/-!
# Transferring a local exchange to the difference of natural densities

The reciprocal-mass gain holds for every larger smooth template. Taking
suprema and applying the two-sided density comparisons subtracts only the
actual prime-square tail from the rough density factor times the gain.
-/

namespace GRHArticle.ProgressionFree

/-- A gain on every rational-ratio template gives the same unnormalized
gain at every larger prime cutoff. -/
theorem integerBoundaryGain_smoothOptimization {B : Set ℕ} (g : ℝ)
    (hB : B ⊆ Nat.smoothNumbers 6) (hb : IntegerPrefixAdmissible true B)
    (hgain : ∀ A ⊆ Nat.smoothNumbers 6, IntegerPrefixAdmissible false A →
      g ≤ integerExchangeReciprocalWeight B - integerExchangeReciprocalWeight A -
        integerExchangeCharge * integerExchangeReciprocalWeight (B \ A))
    {Y : ℕ} (hY : 5 ≤ Y) :
    integerSmoothLowerOptimization false Y + integerSmoothDensityFactor Y * g ≤
      integerSmoothLowerOptimization true Y := by
  let weights (integral : Bool) : Set ℝ := {w | ∃ A : Set ℕ, A ⊆ Nat.smoothNumbers (Y+1) ∧
    IntegerPrefixAdmissible integral A ∧ w = integerExchangeReciprocalWeight A}
  have hW : (weights false).Nonempty := ⟨_,∅,Set.empty_subset _,by intro a b c ha; exact ha.elim,rfl⟩
  have hI : BddAbove (weights true) := by
    refine ⟨(integerSmoothDensityFactor Y)⁻¹,?_⟩
    rintro _ ⟨E,hE,_,rfl⟩
    exact smoothSubset_reciprocal_le hE
  have h : sSup (weights false) ≤ sSup (weights true) - g := by
    apply csSup_le hW
    rintro _ ⟨E,hE,he,rfl⟩
    let A := E ∩ Nat.smoothNumbers 6
    have ha : IntegerPrefixAdmissible false A := fun _ _ _ hx hy hz ↦ he hx.1 hy.1 hz.1
    have hl := integerBoundaryPatch_weight hY hE hB g (hgain A (fun _ hx ↦ hx.2) ha)
    have hF : integerBoundaryPatch E B ⊆ Nat.smoothNumbers (Y+1) := fun _ h ↦
      h.1.elim (fun b ↦ Nat.smoothNumbers_mono (by omega : 6 ≤ Y+1) (hB b)) (fun e ↦ hE e.1)
    have hu := le_csSup hI (show integerExchangeReciprocalWeight (integerBoundaryPatch E B) ∈ weights true from
      ⟨_, hF, integerBoundaryPatch_admissible hY hE hB he hb,rfl⟩)
    linarith only [hl,hu]
  change integerSmoothDensityFactor Y * sSup (weights false) + integerSmoothDensityFactor Y * g ≤
    integerSmoothDensityFactor Y * sSup (weights true)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mp h) (integerSmoothDensityFactor_pos Y).le

/-- The large-prime loss in the difference of actual natural-density
suprema is at most the sum of the omitted reciprocal prime squares. -/
theorem integerBoundaryGain_density_bridge {B : Set ℕ} (g : ℝ)
    (hB : B ⊆ Nat.smoothNumbers 6) (hb : IntegerPrefixAdmissible true B)
    (hgain : ∀ A ⊆ Nat.smoothNumbers 6, IntegerPrefixAdmissible false A →
      g ≤ integerExchangeReciprocalWeight B - integerExchangeReciprocalWeight A -
        integerExchangeCharge * integerExchangeReciprocalWeight (B \ A))
    {Y : ℕ} (hY : 5 ≤ Y) :
    integerSmoothDensityFactor Y * g - integerPrimeSquareTail Y ≤
      integerNaturalDensitySupremum true - integerNaturalDensitySupremum false := by
  have hs := integerBoundaryGain_smoothOptimization g hB hb hgain hY
  have hI := (integerSmoothLowerOptimization_error true Y).2
  have hQ := integerNaturalDensitySupremum_le_smoothLower false Y
  linarith only [hs,hI,hQ]

end GRHArticle.ProgressionFree
