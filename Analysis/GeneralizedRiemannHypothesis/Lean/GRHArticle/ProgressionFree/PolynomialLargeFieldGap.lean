import GRHArticle.ProgressionFree.PolynomialExceptionalBall
import GRHArticle.ProgressionFree.PolynomialLargeFieldBall
import GRHArticle.ProgressionFree.PolynomialCounterexample
import GRHArticle.ProgressionFree.PolynomialSupremum

/-!
# The extremal polynomial density at large field size

Count exceptional targets once per degree across the full ball. Only
the linear degree requires the larger exceptional probability. An
arbitrary depth cutoff gives a family of bounds for the actual supremum.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Finset Filter Topology
open scoped Classical

variable (F : Type*) [Field F] [Fintype F]

private theorem polynomialBallProportion_le_largeField_sum
    (hq : 16 ≤ Fintype.card F) {E : Set F[X]} (hE : PolynomialRatioThreeGPFree E)
    {K N : ℕ} (hKN : K ≤ N) :
    let q := (Fintype.card F : ℝ)
    polynomialBallProportion E N ≤ polynomialBallProportion (polynomialDeficitSet (F := F) greedyExponents N) N +
      (∑ d ∈ Icc 1 (K/2), polynomialExceptionalBound (Fintype.card F) d) + q⁻¹^(K+1) := by
  let I := Icc 1 (K/2)
  let step (k : ℕ) := if h : k ∉ greedyExponents then (exists_polynomialLayerStep_greedy h).choose else 0
  have hs (k : ℕ) (hk : k ≤ K) (hc : k ∉ greedyExponents) :
      step k ∈ I ∧ PolynomialLayerStep greedyExponents k (step k) := by
    have h := (exists_polynomialLayerStep_greedy hc).choose_spec
    simp only [step,dif_pos hc]
    exact ⟨mem_Icc.mpr ⟨h.1,by have := h.2.1; omega⟩, h⟩
  have hpos (d : ℕ) (hd : d ∈ I) : 0 < d := (mem_Icc.mp hd).1
  have hpr (d : ℕ) (hd : d ∈ I) : (polynomialDegreePrimes F d).Nonempty := by
    rw [← card_pos,card_polynomialDegreePrimes]
    by_contra! he
    have hl := pow_card_le_twice_degree_mul_polynomialIrreducibleCount F d (hpos d hd)
    have : 0 < Fintype.card F ^ d := pow_pos Fintype.card_pos _
    simp [Nat.eq_zero_of_le_zero he] at hl
  have hc := card_polynomialBall_le_preferred_add_exceptional hE threeAPFree_greedyExponents N K I step
    (polynomialDegreePrimes F) (polynomialExceptionalBall F N) (polynomialExceptionalTheta (Fintype.card F))
    hs (fun d _ ↦ polynomialExceptionalTheta_nonneg hq d)
    (sum_polynomialExceptionalTheta_le_one hq I hpos) (fun d hd ↦ ⟨hpr d hd, fun p hp ↦
      let h := mem_polynomialDegreePrimes.mp hp
      ⟨h.1.ne_zero,h.2.2⟩⟩) (by
      intro d _ g hg hx
      rw [card_polynomialDegreePrimes]
      apply le_of_not_gt
      intro he
      exact hx (mem_polynomialExceptionalBall.mpr ⟨hg.1,hg.2.1,
        (polynomialExceptionalThreshold_le_iff hq d _).mpr he⟩))
  let q := (Fintype.card F : ℝ)
  have hq₀ : 0 < q := by dsimp [q]; positivity
  have htail : q^(N-K) = q⁻¹^(K+1)*q^(N+1) := by
    have hn : N+1 = (K+1)+(N-K) := by omega
    calc
      _ = (q^(K+1))⁻¹ * (q^(K+1)*q^(N-K)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq₀.ne'), one_mul]
      _ = _ := by rw [← pow_add, ← hn, inv_pow]
  have hsum : (∑ d ∈ I, ((polynomialExceptionalBall F N d).card : ℝ)) ≤
      (∑ d ∈ I, polynomialExceptionalBound (Fintype.card F) d) * q^(N+1) := by
    rw [Finset.sum_mul]
    exact sum_le_sum fun d hd ↦ (card_polynomialExceptionalBall_le F hq N d (hpos d hd)).trans_eq (mul_comm _ _)
  let B := polynomialDegreeLTFinset F (N+1)
  let c := ((B.filter (· ∈ E)).card : ℝ)
  let g := ((B.filter (· ∈ polynomialDeficitSet (F := F) greedyExponents N)).card : ℝ)
  let e := ∑ d ∈ I, polynomialExceptionalBound (Fintype.card F) d
  change c / q^(N+1) ≤ g / q^(N+1) + e + q⁻¹^(K+1)
  apply (div_le_iff₀ (pow_pos hq₀ _)).mpr
  rw [add_mul,add_mul,div_mul_cancel₀ _ (pow_ne_zero _ hq₀.ne'),← htail]
  exact hc.trans (by change g + _ + _ ≤ g + _ + _; linarith only [hsum])

/-- For any depth cutoff, the supremum exceeds the benchmark by at most
the sum of the distinct prime-degree exceptional rates and the deep-layer loss. -/
theorem polynomialRatioDensitySupremum_gap_le_cutoff (hq : 16 ≤ Fintype.card F) (K : ℕ) :
    polynomialRatioDensitySupremum F - polynomialDegreeBenchmark F ≤
      (∑ d ∈ Icc 1 (K/2), polynomialExceptionalBound (Fintype.card F) d) +
        (Fintype.card F : ℝ)⁻¹^(K+1) := by
  obtain ⟨E, _, hE, he⟩ := polynomialRatioDensitySupremum_attained F
  have hbase := tendsto_polynomialBallProportion_deficit (F := F) greedyExponents
  let b := ∑ d ∈ Icc 1 (K/2), polynomialExceptionalBound (Fintype.card F) d
  let t := (Fintype.card F : ℝ)⁻¹^(K+1)
  have hlim := (hbase.add_const b).add_const t
  have hN := (eventually_ge_atTop K).mono fun N hKN ↦
    polynomialBallProportion_le_largeField_sum F hq hE hKN
  have hupper := (limsup_le_limsup hN (isCoboundedUnder_le_of_le atTop (polynomialBallProportion_nonneg E))
    hlim.isBoundedUnder_le).trans_eq hlim.limsup_eq
  change limsup (polynomialBallProportion E) atTop ≤ polynomialDegreeBenchmark F + b + t at hupper
  rw [he] at hupper
  change _ ≤ b+t
  linarith

/-- A sharper explicit gap than `gpp:thm:largeq`. Only the linear-prime
term carries the factor `q^14`. -/
theorem polynomialRatioDensitySupremum_largeField_sharp (hq : 16 ≤ Fintype.card F) :
    let q := Fintype.card F
    polynomialRatioDensitySupremum F - polynomialDegreeBenchmark F ≤
      (q:ℝ)⁻¹^(q-14) + ((q/2-1:ℕ):ℝ)*(q:ℝ)⁻¹^q + (q:ℝ)⁻¹^(q+1) := by
  let q := Fintype.card F
  have hi : 1 ∈ Icc 1 (q/2) := mem_Icc.mpr ⟨le_rfl, by dsimp [q]; omega⟩
  have hsum : (∑ d ∈ Icc 1 (q/2), polynomialExceptionalBound q d) =
      (q:ℝ)⁻¹^(q-14) + ((q/2-1:ℕ):ℝ)*(q:ℝ)⁻¹^q := by
    rw [← add_sum_erase _ _ hi]
    simp only [polynomialExceptionalBound]
    congr 1
    calc
      _ = ∑ _d ∈ (Icc 1 (q/2)).erase 1, (q:ℝ)⁻¹^q := by
        apply sum_congr rfl
        intro d hd
        rw [if_neg (mem_erase.mp hd).1]
      _ = _ := by simp
  exact (polynomialRatioDensitySupremum_gap_le_cutoff F hq q).trans_eq (congrArg (· + _) hsum)

/-- The strict positive gap and published upper bound in `gpp:thm:largeq`. -/
theorem polynomialRatioDensitySupremum_largeField (hq : 16 ≤ Fintype.card F) :
    let q := Fintype.card F
    0 < polynomialRatioDensitySupremum F - polynomialDegreeBenchmark F ∧
      polynomialRatioDensitySupremum F - polynomialDegreeBenchmark F ≤
        (2*(q:ℝ)+1)*(q:ℝ)⁻¹^(q-14) := by
  let q := Fintype.card F
  let z := (q:ℝ)⁻¹
  have hz₀ : 0 ≤ z := by dsimp [z]; positivity
  have hz₁ : z ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α := F))
  have hc : (((q/2-1:ℕ):ℝ)) ≤ (q:ℝ) := by exact_mod_cast (show q/2-1 ≤ q by omega)
  have hd : z^q ≤ z^(q-14) := pow_le_pow_of_le_one hz₀ hz₁ (by omega)
  have ht : z^(q+1) ≤ z^(q-14) := pow_le_pow_of_le_one hz₀ hz₁ (by omega)
  have hq' : 1 ≤ (q:ℝ) := by exact_mod_cast Fintype.card_pos (α := F)
  refine ⟨sub_pos.mpr (polynomialDegreeBenchmark_lt_polynomialRatioDensitySupremum F),
    (polynomialRatioDensitySupremum_largeField_sharp F hq).trans ?_⟩
  change z^(q-14) + _*z^q + z^(q+1) ≤ (2*(q:ℝ)+1)*z^(q-14)
  have hm := mul_le_mul hc hd (pow_nonneg hz₀ _) (Nat.cast_nonneg q)
  have h := mul_le_mul_of_nonneg_right hq' (pow_nonneg hz₀ (q-14))
  linarith only [hm,ht,h]

end GRHArticle.ProgressionFree
