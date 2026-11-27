import GRHArticle.ProgressionFree.IntegerUpperDensityLowerBound
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The exact squarefree rough Euler density

Finite local rules exclude primes up to `Y` and exclude squares of larger
primes up to the truncation. The omitted prime squares have uniformly
vanishing density, so the finite local products give the exact limit.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- The correction `v_Y` obtained by requiring squarefreeness outside the cutoff. -/
noncomputable def integerSquarefreeRoughFactor (Y : ℕ) : ℝ :=
  ∏' p : ℕ, (1 - integerPrimeSquareTerm Y p)

private noncomputable def squarefreeRoughFactorPrefix (Y K : ℕ) : ℝ :=
  ∏ p ∈ range (K+1), (1 - integerPrimeSquareTerm Y p)

private theorem tendsto_squarefreeRoughFactorPrefix (Y : ℕ) :
    Tendsto (squarefreeRoughFactorPrefix Y) atTop (𝓝 (integerSquarefreeRoughFactor Y)) := by
  have hm : Multipliable (fun p ↦ 1 - integerPrimeSquareTerm Y p) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable
      ((summable_integerPrimeSquareTerm Y).neg)
  exact hm.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)

private theorem integerPrimeSquareTerm_le_one (Y p : ℕ) : integerPrimeSquareTerm Y p ≤ 1 := by
  unfold integerPrimeSquareTerm
  split
  · rename_i hp
    have h₁ : 1 ≤ (p:ℝ) := by exact_mod_cast hp.2.one_lt.le
    have h₀ : 0 < (p:ℝ) := lt_of_lt_of_le (by norm_num) h₁
    exact (div_le_one (pow_pos h₀ _)).mpr (one_le_pow₀ h₁)
  · norm_num

/-- The squarefree correction lies between zero and one. -/
theorem integerSquarefreeRoughFactor_mem_unitInterval (Y : ℕ) :
    integerSquarefreeRoughFactor Y ∈ Set.Icc 0 1 := by
  have h₀ (p : ℕ) : 0 ≤ 1 - integerPrimeSquareTerm Y p :=
    sub_nonneg.mpr (integerPrimeSquareTerm_le_one Y p)
  have h₁ (p : ℕ) : 1 - integerPrimeSquareTerm Y p ≤ 1 :=
    sub_le_self _ (integerPrimeSquareTerm_nonneg Y p)
  exact ⟨ge_of_tendsto' (tendsto_squarefreeRoughFactorPrefix Y)
    (fun _ ↦ Finset.prod_nonneg fun p _ ↦ h₀ p),
    le_of_tendsto' (tendsto_squarefreeRoughFactorPrefix Y)
      (fun _ ↦ Finset.prod_le_one (fun p _ ↦ h₀ p) (fun p _ ↦ h₁ p))⟩

/-- Removing large prime squares loses at most the sum of their reciprocal squares. -/
theorem one_sub_integerSquarefreeRoughFactor_le_primeSquareTail (Y : ℕ) :
    1 - integerSquarefreeRoughFactor Y ≤ integerPrimeSquareTail Y := by
  have h₀ (p : ℕ) : 0 ≤ 1 - integerPrimeSquareTerm Y p :=
    sub_nonneg.mpr (integerPrimeSquareTerm_le_one Y p)
  have h₁ (p : ℕ) : 1 - integerPrimeSquareTerm Y p ≤ 1 :=
    sub_le_self _ (integerPrimeSquareTerm_nonneg Y p)
  have hfinite (S : Finset ℕ) : 1 - (∏ p ∈ S, (1 - integerPrimeSquareTerm Y p)) ≤
      ∑ p ∈ S, integerPrimeSquareTerm Y p := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
      rw [prod_insert hp, sum_insert hp]
      let P := ∏ q ∈ S, (1 - integerPrimeSquareTerm Y q)
      have hP : P ≤ 1 := Finset.prod_le_one (fun q _ ↦ h₀ q) (fun q _ ↦ h₁ q)
      calc
        _ = (1-P) + integerPrimeSquareTerm Y p * P := by dsimp only [P]; ring
        _ ≤ (∑ q ∈ S, integerPrimeSquareTerm Y q) + integerPrimeSquareTerm Y p :=
          add_le_add ih (mul_le_of_le_one_right (integerPrimeSquareTerm_nonneg Y p) hP)
        _ = _ := add_comm _ _
  apply le_of_tendsto' (tendsto_const_nhds.sub (tendsto_squarefreeRoughFactorPrefix Y))
  intro K
  exact (hfinite (range (K+1))).trans
    ((summable_integerPrimeSquareTerm Y).sum_le_tsum _ (fun p _ ↦ integerPrimeSquareTerm_nonneg Y p))

private def squarefreeRoughTruncation (Y K : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p ∈ Nat.primesLE K,
    if p ≤ Y then n.factorization p = 0 else n.factorization p ≤ 1}

private theorem mem_squarefreeRoughNumbers_iff {Y n : ℕ} :
    n ∈ integerSquarefreeRoughNumbers Y ↔ n ≠ 0 ∧ ∀ p, p.Prime →
      if p ≤ Y then n.factorization p = 0 else n.factorization p ≤ 1 := by
  simp only [integerSquarefreeRoughNumbers, Set.mem_setOf_eq, integerRoughNumbers_eq_valuationCylinder]
  constructor
  · rintro ⟨⟨hn,hsmall⟩,hsf⟩
    refine ⟨hn, fun p hp ↦ ?_⟩
    by_cases hY : p ≤ Y
    · exact if_pos hY ▸ hsmall p (Nat.mem_primesLE.mpr ⟨hY,hp⟩)
    · exact if_neg hY ▸ hsf.natFactorization_le_one p
  · rintro ⟨hn,h⟩
    refine ⟨⟨hn, fun p hp ↦ ?_⟩, (Nat.squarefree_iff_factorization_le_one hn).mpr ?_⟩
    · obtain ⟨hY,hp⟩ := Nat.mem_primesLE.mp hp
      simpa only [if_pos hY] using h p hp
    · intro p
      by_cases hp : p.Prime
      · by_cases hY : p ≤ Y
        · have hz : n.factorization p = 0 := by simpa only [if_pos hY] using h p hp
          simp [hz]
        · simpa only [if_neg hY] using h p hp
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem absolute_density_squarefreeRoughTruncation_le {Y K N : ℕ} (hYK : Y ≤ K) (hK : 0 < K) :
    |densityUpTo (integerSquarefreeRoughNumbers Y) N - densityUpTo (squarefreeRoughTruncation Y K) N| ≤
      1/(K:ℝ) := by
  refine (densityUpTo_abs_sub_le_of_symmDiff_subset N (E := {n | ∃ p : ℕ, K < p ∧ p.Prime ∧ p^2 ∣ n})
    ?_).trans (densityUpTo_largePrimeSquare_le K N hK)
  intro n hn
  rcases hn with ⟨hn, hnot⟩ | ⟨hn, hnot⟩
  · obtain ⟨hn₀,h⟩ := mem_squarefreeRoughNumbers_iff.mp hn
    exact (hnot ⟨hn₀, fun p hp ↦ h p (Nat.mem_primesLE.mp hp).2⟩).elim
  · by_contra hbad
    apply hnot
    refine mem_squarefreeRoughNumbers_iff.mpr ⟨hn.1, fun p hp ↦ ?_⟩
    by_cases h : p ≤ K
    · exact hn.2 p (Nat.mem_primesLE.mpr ⟨h,hp⟩)
    · have hY : ¬ p ≤ Y := fun hpY ↦ h (hpY.trans hYK)
      simp only [if_neg hY]
      apply Nat.lt_succ_iff.mp
      by_contra! htwo
      exact hbad ⟨p, Nat.lt_of_not_ge h, hp, (hp.pow_dvd_iff_le_factorization hn.1).mpr htwo⟩

private theorem hasNaturalDensity_squarefreeRoughTruncation (Y K : ℕ) (hYK : Y ≤ K) :
    HasNaturalDensity (squarefreeRoughTruncation Y K)
      (integerSmoothDensityFactor Y * squarefreeRoughFactorPrefix Y K) := by
  let S := Nat.primesLE K
  let A (p : ↥S) : Finset ℕ := if p.val ≤ Y then {0} else {0,1}
  have hD := hasNaturalDensity_finite_prime_rules S A fun p hp ↦ (Nat.mem_primesLE.mp hp).2
  have hA (p : ↥S) (j : ℕ) : j ∈ A p ↔ if p.val ≤ Y then j = 0 else j ≤ 1 := by
    by_cases h : p.val ≤ Y
    · simp [A,h]
    · simp only [A, if_neg h, mem_insert, mem_singleton]
      omega
  have hset : {n | n ≠ 0 ∧ ∀ p : ↥S, n.factorization p.val ∈ A p} = squarefreeRoughTruncation Y K := by
    ext n
    simp only [squarefreeRoughTruncation, Set.mem_setOf_eq, hA]
    exact and_congr_right fun _ ↦ ⟨fun h p hp ↦ h ⟨p,hp⟩, fun h p ↦ h p.val p.property⟩
  rw [hset] at hD
  let f (p : ℕ) : ℝ := if p ≤ Y then 1 - (p:ℝ)⁻¹ else 1 - 1/(p:ℝ)^2
  have hLocal (p : ↥S) :
      (1 - 1/(p.val:ℝ)) * ∑ e ∈ A p, (1/(p.val:ℝ))^e = f p.val := by
    by_cases h : p.val ≤ Y
    · simp [A, f, h, one_div]
    · simp only [A, if_neg h, f, sum_pair (show (0:ℕ) ≠ 1 by decide), pow_zero, pow_one, one_div, ← inv_pow]
      ring
  simp_rw [hLocal] at hD
  rw [Finset.univ_eq_attach, Finset.prod_attach S f] at hD
  have hsmall : S.filter (· ≤ Y) = Nat.primesLE Y := by
    ext p
    simp only [S, mem_filter, Nat.mem_primesLE]
    exact ⟨fun h ↦ ⟨h.2,h.1.2⟩, fun h ↦ ⟨⟨h.1.trans hYK,h.2⟩,h.1⟩⟩
  have hlarge : S.filter (fun p ↦ ¬p ≤ Y) =
      (range (K+1)).filter (fun p ↦ Y < p ∧ p.Prime) := by
    ext p
    simp only [S, mem_filter, Nat.mem_primesLE, mem_range, Nat.lt_succ_iff, not_le]
    tauto
  have hfactor : (∏ p ∈ S, f p) = integerSmoothDensityFactor Y * squarefreeRoughFactorPrefix Y K := by
    rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Y) f, hsmall, hlarge]
    congr 1
    · apply prod_congr rfl
      intro p hp
      exact if_pos (Nat.mem_primesLE.mp hp).1
    · rw [Finset.prod_filter, squarefreeRoughFactorPrefix]
      apply prod_congr rfl
      intro p _
      by_cases hp : Y < p ∧ p.Prime
      · simp [f, hp, not_le.mpr hp.1, integerPrimeSquareTerm]
      · simp [hp, integerPrimeSquareTerm]
  rwa [hfactor] at hD

/-- The density of the squarefree rough kernels is `c_Y * v_Y`. -/
theorem hasNaturalDensity_integerSquarefreeRoughNumbers (Y : ℕ) :
    HasNaturalDensity (integerSquarefreeRoughNumbers Y)
      (integerSmoothDensityFactor Y * integerSquarefreeRoughFactor Y) := by
  let c := integerSmoothDensityFactor Y
  let v := integerSquarefreeRoughFactor Y
  let U := integerSquarefreeRoughNumbers Y
  change Tendsto (densityUpTo U) atTop (𝓝 (c*v))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε₃ : 0 < ε/3 := by positivity
  have happr := Metric.tendsto_nhds.mp (tendsto_const_nhds.mul (tendsto_squarefreeRoughFactorPrefix Y)
    (f := fun _ : ℕ ↦ c)) (ε/3) hε₃
  have hinv := (tendsto_order.mp (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).2 (ε/3) hε₃
  have hc : ∀ᶠ K : ℕ in atTop, Y ≤ K ∧ 0 < K ∧ 1/(K:ℝ) < ε/3 ∧
      |c*squarefreeRoughFactorPrefix Y K - c*v| < ε/3 := by
    filter_upwards [eventually_ge_atTop (max Y 1), hinv, happr] with K hK hi hh
    exact ⟨(le_max_left _ _).trans hK, (le_max_right _ _).trans hK, hi, by simpa [Real.dist_eq,v] using hh⟩
  obtain ⟨K,hYK,hK,hi,hcK⟩ := hc.exists
  have htr := Metric.tendsto_nhds.mp (hasNaturalDensity_squarefreeRoughTruncation Y K hYK)
    (ε/3) hε₃
  filter_upwards [htr] with N hn
  rw [Real.dist_eq] at hn ⊢
  have hdiff := absolute_density_squarefreeRoughTruncation_le (N := N) hYK hK
  let T := densityUpTo (squarefreeRoughTruncation Y K) N
  let D := c*squarefreeRoughFactorPrefix Y K
  calc
    _ ≤ |densityUpTo U N - T| + |T - D| + |D - c*v| := by
      have h₁ := abs_sub_le (densityUpTo U N) D (c*v)
      have h₂ := abs_sub_le (densityUpTo U N) T D
      linarith only [h₁,h₂]
    _ < ε := by linarith only [hdiff,hi,hn,hcK]

/-- The multiplicative lower bound `v_Y U_Y ≤ u` of the smooth-factor bound. -/
theorem integerSquarefreeRoughFactor_mul_integerSmoothUpperOptimization_le_integerUpperDensitySupremum
    (integral : Bool) (Y : ℕ) :
    integerSquarefreeRoughFactor Y * integerSmoothUpperOptimization integral Y ≤
      integerUpperDensitySupremum integral := by
  have hr : integerSquarefreeRoughNumbers Y ⊆ integerRoughNumbers Y := fun _ h ↦ h.1
  have h := smoothPrefixWeightedSum_sub_le_integerUpperDensitySupremum integral Y hr hr
    (fun _ h ↦ h.2) (hasNaturalDensity_integerSquarefreeRoughNumbers Y)
    (err := 0) (fun _ ↦ by rw [add_zero])
  simpa only [integerSmoothUpperOptimization, sub_zero, ← mul_assoc,
    mul_comm (integerSquarefreeRoughFactor Y) (integerSmoothDensityFactor Y)] using h

end GRHArticle.ProgressionFree
