import GRHArticle.ProgressionFree.PolynomialEulerTail
import GRHArticle.ProgressionFree.PolynomialSmoothApproximation

/-!
# Bounding the finite-prime density approximation by one

Replacing each smooth-ball optimum by the size of its entire ball gives the
product of the smooth degree series and the ordinary geometric series.
Both factors cancel against the normalization in the approximation.
-/

namespace GRHArticle.ProgressionFree

open Polynomial
open scoped BigOperators

variable (F : Type*) [Field F] [Fintype F] [decF : DecidableEq F]

/-- Partition a monic smooth ball by its actual degree. -/
theorem card_polynomialSmoothBall_eq_sum (T t : ℕ) :
    (polynomialSmoothBall F T t).card = ∑ d ∈ Finset.range (t+1),
      PowerSeries.coeff (R := ℕ) d (polynomialSmoothDegreeSeries F T) := by
  have hdec : decF = Classical.decEq F := Subsingleton.elim _ _
  subst decF
  classical
  let B := polynomialSmoothBall F T t
  have h (f : Polynomial F) (hf : f ∈ B) : f.natDegree ∈ Finset.range (t+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_polynomialSmoothBall.mp hf).2.1)
  rw [Finset.card_eq_sum_card_fiberwise h]
  apply Finset.sum_congr rfl
  intro d hd
  rw [coeff_polynomialSmoothDegreeSeries_eq_card]
  congr 1
  ext f
  simp only [Finset.mem_filter, B, mem_polynomialSmoothBall, mem_polynomialSmoothLayer]
  have hdt : d ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  exact ⟨fun ⟨⟨hm, _, hs⟩, he⟩ ↦ ⟨hm, he, hs⟩,
    fun ⟨hm, he, hs⟩ ↦ ⟨⟨hm, he ▸ hdt, hs⟩, he⟩⟩

/-- The upper approximation is itself between zero and one. -/
theorem polynomialDensityUpperApproximation_mem_unitInterval (T : ℕ) :
    0 ≤ polynomialDensityUpperApproximation F T ∧ polynomialDensityUpperApproximation F T ≤ 1 := by
  have hdec : decF = Classical.decEq F := Subsingleton.elim _ _
  subst decF
  classical
  let w := (Fintype.card F : ℝ)⁻¹
  let S := polynomialSmoothPrimes F T
  let H := polynomialSmoothDegreeSeries F T
  let c := ∏ p ∈ S, (1 - w^p.natDegree)
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hw₀ : 0 ≤ w := by dsimp [w]; positivity
  have hw : w < 1 := inv_lt_one_of_one_lt₀ hq
  have hd (p : Polynomial F) (hp : p ∈ S) : 0 < p.natDegree :=
    (mem_polynomialSmoothPrimes.mp hp).2.1.natDegree_pos
  have hc : 0 < c := Finset.prod_pos fun p hp ↦ sub_pos.mpr (pow_lt_one₀ hw₀ hw (hd p hp).ne')
  have h1 : 0 < 1-w := sub_pos.mpr hw
  have hmass := (hasTiltedDegreeMoments_smooth S natDegree hd hw₀ hw).mass
  change HasSum (tiltedDegreeTerm H w) _ at hmass
  have hs : HasSum (tiltedDegreeTerm H w) c⁻¹ := by
    simpa only [c, one_div, Finset.prod_inv_distrib] using hmass
  have hg := hasSum_geometric_of_lt_one hw₀ hw
  have hconv := hasSum_sum_range_mul_of_summable_norm hs.summable.norm hg.summable.norm
  rw [hs.tsum_eq, hg.tsum_eq] at hconv
  have hb (t : ℕ) : ∑ k ∈ Finset.range (t+1), tiltedDegreeTerm H w k * w^(t-k) =
      ((polynomialSmoothBall F T t).card : ℝ) * w^t := by
    rw [card_polynomialSmoothBall_eq_sum, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have he : k + (t-k) = t := Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    rw [tiltedDegreeTerm, mul_assoc, ← pow_add, he]
  simp_rw [hb] at hconv
  have hJ : ∀ t, (polynomialSmoothMaximum F T t : ℝ) * w^t ≤
      ((polynomialSmoothBall F T t).card : ℝ) * w^t := by
    intro t
    obtain ⟨A, hsub, _, he⟩ := exists_polynomialSmoothMaximum (F := F) T t
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hw₀ t)
    rw [← he]
    exact_mod_cast Finset.card_le_card hsub
  have hlu := (summable_polynomialSmoothMaximum_weight (F := F) T).tsum_le_tsum hJ hconv.summable
  rw [hconv.tsum_eq] at hlu
  change 0 ≤ (1-w)*c*_ ∧ (1-w)*c*_ ≤ 1
  refine ⟨mul_nonneg (mul_nonneg h1.le hc.le) (tsum_nonneg (fun n ↦ by positivity)), ?_⟩
  calc
    _ ≤ (1-w)*c*(c⁻¹*(1-w)⁻¹) := mul_le_mul_of_nonneg_left hlu (mul_nonneg h1.le hc.le)
    _ = 1 := by field_simp [h1.ne',hc.ne']

end GRHArticle.ProgressionFree
