import GRHArticle.ProgressionFree.IntegerNaturalDensityApproximation
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.NumberTheory.Harmonic.Bounds

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

private noncomputable def logWeight (n : ℕ) : ℝ := 1/((n:ℝ)+2)

private theorem logWeight_bounds {N : ℕ} (hN : 0 < N) :
    Real.log N - 1 ≤ ∑ k ∈ range N, logWeight k ∧
      (∑ k ∈ range N, logWeight k) ≤ Real.log N + 1 := by
  have hshift : (∑ k ∈ range N, logWeight k) + 1 = (harmonic (N+1) : ℝ) := by
    rw [harmonic, Rat.cast_sum, sum_range_succ']
    simp [logWeight, one_div, Nat.cast_add, add_assoc]
  rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hshift
  have hl : Real.log N ≤ (harmonic N : ℝ) :=
    (Real.log_le_log (Nat.cast_pos.mpr hN) (Nat.cast_le.mpr (Nat.le_succ N))).trans (log_add_one_le_harmonic N)
  have hu := harmonic_le_one_add_log N
  have hp : 0 ≤ (((N+1 : ℕ):ℝ))⁻¹ := by positivity
  have h₁ : (((N+1 : ℕ):ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))
  constructor <;> linarith

private theorem log_nat_atTop : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem logWeight_sum_ratio :
    Tendsto (fun N : ℕ ↦ (∑ k ∈ range N, logWeight k) / Real.log N) atTop (𝓝 1) := by
  have hz := log_nat_atTop.const_div_atTop 1
  have hl := (tendsto_const_nhds (x := (1:ℝ))).sub hz
  have hu := (tendsto_const_nhds (x := (1:ℝ))).add hz
  rw [sub_zero] at hl
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hp : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [le_div_iff₀ hp, sub_mul, one_mul, div_mul_cancel₀ _ hp.ne']
    exact (logWeight_bounds (by omega)).1
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hp : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [div_le_iff₀ hp, add_mul, one_mul, div_mul_cancel₀ _ hp.ne']
    exact (logWeight_bounds (by omega)).2

/-- Natural density implies the same logarithmic density using positive
integers through `N` and the normalization `log N`. -/
theorem tendsto_integerLogDensityUpTo_of_naturalDensity {A : Set ℕ} {d : ℝ}
    (hd : HasNaturalDensity A d) : Tendsto (integerLogDensityUpTo A) atTop (𝓝 d) := by
  let f (k : ℕ) := densityUpTo A (k+1)-d
  have hf : Tendsto f atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr (hd.comp (tendsto_add_atTop_nat 1))
  have hsumdiv : Tendsto (fun N ↦ ∑ k ∈ range N, logWeight k) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_atTop_add_const_right atTop (-1:ℝ) log_nat_atTop)
    filter_upwards [eventually_gt_atTop 0] with N hN using (logWeight_bounds hN).1
  have ho : (fun k ↦ f k * logWeight k) =o[atTop] logWeight := by
    simpa only [one_mul] using ((isLittleO_one_iff ℝ).mpr hf).mul_isBigO (isBigO_refl logWeight atTop)
  have hs := ho.sum_range (fun k ↦ by unfold logWeight; positivity) hsumdiv
  have heq := (isEquivalent_iff_tendsto_one (log_nat_atTop.eventually_ne_atTop 0)).mpr logWeight_sum_ratio
  have hrem := (hs.trans_isBigO heq.isBigO).tendsto_div_nhds_zero
  let b (N : ℕ) := (countUpTo A N : ℝ) / ((N:ℝ)+1) / Real.log N
  have hb : Tendsto b atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (log_nat_atTop.const_div_atTop 1)
    · filter_upwards [eventually_gt_atTop 1] with N hN
      exact div_nonneg (by positivity) (Real.log_pos (by exact_mod_cast hN)).le
    · filter_upwards [eventually_gt_atTop 1] with N hN
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by exact_mod_cast hN)).le
      apply (div_le_one (by positivity)).mpr
      exact (by exact_mod_cast countUpTo_le_cutoff A N : (countUpTo A N:ℝ) ≤ N).trans
        (le_add_of_nonneg_right zero_le_one)
  have h := (hb.add hrem).add (logWeight_sum_ratio.const_mul d)
  rw [zero_add, mul_one, zero_add] at h
  refine h.congr fun N ↦ ?_
  unfold integerLogDensityUpTo
  rw [reciprocalMassUpTo_partial_summation]
  simp only [f, sub_mul, sum_sub_distrib, ← mul_sum, b, add_div, sub_div]
  simp only [logWeight, mul_one_div, mul_div_assoc]
  ring

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
