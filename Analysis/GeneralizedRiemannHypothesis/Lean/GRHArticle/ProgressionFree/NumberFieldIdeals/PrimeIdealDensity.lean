import GRHArticle.ProgressionFree.NumberFieldIdeals.LogarithmicDensity
import GRHArticle.ProgressionFree.NumberFieldIdeals.SquarefreeExterior
import Mathlib.NumberTheory.Chebyshev

/-!
# Prime ideals have zero relative natural and logarithmic density

Count primes over each rational prime using the field degree, then apply
Chebyshev's elementary upper bound. The logarithmic estimate measures
the total reciprocal mass of the primes used in a smooth cutoff.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- Prime ideals as a subset of all nonzero integral ideals. -/
def primeIdealSet (K : Type*) [Field K] [NumberField K] : Set (Ideal (𝓞 K))⁰ :=
  Set.range primeIdeal

omit [NumberField K] in
theorem primeIdeal_injective : Function.Injective (primeIdeal (K := K)) :=
  fun _ _ he ↦ HeightOneSpectrum.ext (congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ I.val) he)

theorem idealNormPrefix_primeIdealSet (Y : ℕ) :
    idealNormPrefix (primeIdealSet K) Y = (primesThroughNorm K Y).map ⟨primeIdeal,primeIdeal_injective⟩ := by
  ext I
  simp only [mem_idealNormPrefix,Finset.mem_map,mem_primesThroughNorm,Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨p,rfl⟩,h⟩; exact ⟨p,h,rfl⟩
  · rintro ⟨p,h,rfl⟩; exact ⟨⟨p,rfl⟩,h⟩

/-- Each rational prime has at most the field degree many primes above it. -/
theorem card_primesThroughNorm_le (Y : ℕ) :
    (primesThroughNorm K Y).card ≤ Module.finrank ℚ K * Nat.primeCounting Y := by
  classical
  let S := primesThroughNorm K Y
  let r (p : HeightOneSpectrum (𝓞 K)) := (absNorm p.asIdeal).minFac
  have hmap : ∀ p ∈ S, r p ∈ Nat.primesLE Y := by
    intro p hp
    refine Nat.mem_primesLE.mpr ⟨(Nat.minFac_le (absNorm_pos_of_nonZeroDivisors (primeIdeal p))).trans
      ((mem_primesThroughNorm p Y).mp hp), Nat.minFac_prime ?_⟩
    exact fun h ↦ p.isMaximal.ne_top (absNorm_eq_one_iff.mp h)
  have he := sum_fiberwise_of_maps_to hmap (fun _ ↦ (1:ℕ))
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] at he
  change S.card ≤ _
  rw [← he, ← Nat.primesLE_card_eq_primeCounting]
  calc
    _ ≤ ∑ _ ∈ Nat.primesLE Y, Module.finrank ℚ K := by
      apply sum_le_sum
      intro q hq
      apply card_le_finrank_of_prime_dvd_absNorm _ id Function.injective_id.injOn (Nat.prime_of_mem_primesLE hq)
      intro p hp
      exact (mem_filter.mp hp).2 ▸ Nat.minFac_dvd (absNorm p.asIdeal)
    _ = _ := by simp [Nat.mul_comm]

private theorem countUpTo_floor_eq (A : Set (Ideal (𝓞 K))⁰) {X : ℝ} (hX : 0 ≤ X) :
    countUpTo A X = countUpTo A (⌊X⌋₊ : ℝ) := by
  unfold countUpTo
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro I
  simp only [Nat.cast_le, Nat.le_floor_iff hX]

/-- The actual set of nonzero prime ideals has density zero in norm order. -/
theorem hasNaturalDensity_primeIdealSet : HasNaturalDensity (primeIdealSet K) 0 := by
  apply (hasNaturalDensity_iff_tendsto_div _ _).mpr
  rw [zero_mul]
  let C : ℝ := (Module.finrank ℚ K : ℝ) * (Real.log 4 + 1)
  have hlim := Real.tendsto_log_atTop.const_div_atTop C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_gt_atTop 0] with X hX
    exact div_nonneg (Nat.cast_nonneg _) hX.le
  · filter_upwards [eventually_gt_atTop 1,Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1)] with X hX hπ
    have hX' : 0 < X := by linarith
    have hlog := Real.log_pos hX
    rw [countUpTo_floor_eq _ hX'.le, ← card_idealNormPrefix, idealNormPrefix_primeIdealSet, card_map]
    have hcard : ((primesThroughNorm K ⌊X⌋₊).card : ℝ) ≤
        (Module.finrank ℚ K : ℝ) * Nat.primeCounting ⌊X⌋₊ := by exact_mod_cast card_primesThroughNorm_le (K := K) ⌊X⌋₊
    calc
      _ ≤ ((Module.finrank ℚ K : ℝ) * Nat.primeCounting ⌊X⌋₊) / X :=
        div_le_div_of_nonneg_right hcard hX'.le
      _ ≤ ((Module.finrank ℚ K : ℝ) * ((Real.log 4+1) * X / Real.log X)) / X :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hπ (Nat.cast_nonneg _)) hX'.le
      _ = _ := by dsimp [C]; field_simp

/-- Reciprocal prime-ideal norms have sublogarithmic partial sums. -/
theorem tendsto_sum_primeWeight_div_log :
    Tendsto (fun Y : ℕ ↦ (∑ p ∈ primesThroughNorm K Y, primeWeight p) / Real.log Y) atTop (𝓝 0) := by
  simpa only [idealReciprocalMassUpTo, idealNormPrefix_primeIdealSet, sum_map,
    Function.Embedding.coeFn_mk, primeWeight, primeIdeal, zero_mul] using
    tendsto_idealReciprocalMassUpTo_div_log (hasNaturalDensity_primeIdealSet (K := K))

end GRHArticle.ProgressionFree.NumberFieldIdeals
