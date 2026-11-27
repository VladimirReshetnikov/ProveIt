import GRHArticle.ProgressionFree.IntegerNaturalDensityApproximation
import GRHArticle.ProgressionFree.LogarithmicAverages

/-!
# Logarithmic densities of admissible integer sets

Summation by parts transfers natural density to logarithmic density.
The reciprocal bound on each smooth fiber then gives the same supremum
for upper logarithmic density as for natural density.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology Asymptotics

/-- The reciprocal mass up to a cutoff, normalized by its natural logarithm. -/
noncomputable def integerLogDensityUpTo (A : Set ℕ) (N : ℕ) : ℝ :=
  reciprocalMassUpTo A N / Real.log N

/-- Natural density implies the same logarithmic density using positive
integers through `N` and the normalization `log N`. -/
theorem tendsto_integerLogDensityUpTo_of_naturalDensity {A : Set ℕ} {d : ℝ}
    (hd : HasNaturalDensity A d) : Tendsto (integerLogDensityUpTo A) atTop (𝓝 d) := by
  have hm := tendsto_logarithmicAverage_of_tendsto (hd.comp (tendsto_add_atTop_nat 1))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  let b (N : ℕ) := (countUpTo A N : ℝ) / ((N:ℝ)+1) / Real.log N
  have hb : Tendsto b atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hlog.const_div_atTop 1)
    · filter_upwards [eventually_gt_atTop 1] with N hN
      exact div_nonneg (by positivity) (Real.log_pos (by exact_mod_cast hN)).le
    · filter_upwards [eventually_gt_atTop 1] with N hN
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by exact_mod_cast hN)).le
      apply (div_le_one (by positivity)).mpr
      exact (by exact_mod_cast countUpTo_le_cutoff A N : (countUpTo A N:ℝ) ≤ N).trans
        (le_add_of_nonneg_right zero_le_one)
  have h := hb.add hm
  rw [zero_add] at h
  refine h.congr fun N ↦ ?_
  simp only [integerLogDensityUpTo, reciprocalMassUpTo_partial_summation, add_div, b, Function.comp_apply]

/-- Supremum of upper logarithmic densities for a fixed ratio convention. -/
noncomputable def integerUpperLogDensitySupremum (integral : Bool) : ℝ :=
  sSup {d | ∃ A : Set ℕ, 0 ∉ A ∧ IntegerPrefixAdmissible integral A ∧
    d = limsup (integerLogDensityUpTo A) atTop}

private theorem upperLogDensity_le {integral : Bool} {A : Set ℕ}
    (hA : IntegerPrefixAdmissible integral A) : limsup (integerLogDensityUpTo A) atTop ≤
      integerNaturalDensitySupremum integral := by
  apply ge_of_tendsto' (tendsto_integerSmoothLowerOptimization integral)
  intro Y
  let M := integerSmoothLowerOptimization integral Y / integerSmoothDensityFactor Y
  let R := integerRoughNumbers Y
  have hlim := (tendsto_integerLogDensityUpTo_of_naturalDensity (hasNaturalDensity_integerRoughNumbers Y)).const_mul M
  rw [show M * integerSmoothDensityFactor Y = integerSmoothLowerOptimization integral Y from
    div_mul_cancel₀ _ (integerSmoothDensityFactor_pos Y).ne'] at hlim
  rw [← hlim.limsup_eq]
  apply limsup_le_limsup _ _ hlim.isBoundedUnder_le
  · filter_upwards [eventually_gt_atTop 1] with N hN
    unfold integerLogDensityUpTo
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (reciprocalMassUpTo_le_smoothLower integral Y hA N)
      (Real.log_pos (by exact_mod_cast hN)).le
  · apply IsBoundedUnder.isCoboundedUnder_le
    apply isBoundedUnder_of_eventually_ge (a := 0)
    filter_upwards [eventually_gt_atTop 1] with N hN
    exact div_nonneg (sum_nonneg fun _ _ ↦ by positivity) (Real.log_pos (by exact_mod_cast hN)).le

/-- The upper-logarithmic and natural-density suprema are equal under
both McNew ratio conventions. -/
theorem integerUpperLogDensitySupremum_eq_naturalDensitySupremum (integral : Bool) :
    integerUpperLogDensitySupremum integral = integerNaturalDensitySupremum integral := by
  let L := {d : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ IntegerPrefixAdmissible integral A ∧
    d = limsup (integerLogDensityUpTo A) atTop}
  have hE : IntegerPrefixAdmissible integral (∅ : Set ℕ) := by intro a b c ha; exact ha.elim
  have hL : BddAbove L := ⟨_,by rintro _ ⟨A,_,ha,rfl⟩; exact upperLogDensity_le ha⟩
  apply le_antisymm
  · apply csSup_le (show L.Nonempty from ⟨_,∅,by simp,hE,rfl⟩)
    rintro _ ⟨A,_,ha,rfl⟩
    exact upperLogDensity_le ha
  · apply csSup_le (show {d : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ IntegerPrefixAdmissible integral A ∧
        HasNaturalDensity A d}.Nonempty from ⟨0,∅,by simp,hE,hasNaturalDensity_empty⟩)
    rintro d ⟨A,h₀,ha,hd⟩
    exact le_csSup hL ⟨A,h₀,ha,(tendsto_integerLogDensityUpTo_of_naturalDensity hd).limsup_eq.symm⟩

end GRHArticle.ProgressionFree
