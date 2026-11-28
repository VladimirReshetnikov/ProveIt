import GRHArticle.ProgressionFree.PolynomialGreedyCofactorCount
import GRHArticle.ProgressionFree.PolynomialRoughWeightLimit

/-!
# Normalized limits of greedy cofactor layers

After separating the low ternary digit, the squarefree coefficient gives
the limit. The cubic factor contributes a summable weight since its
degree is tripled.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The normalized greedy cofactor constant with the specified primes excluded. -/
noncomputable def greedyPrimeAvoidingDensity (S : Finset F[X]) : ℝ :=
  let z := (Fintype.card F : ℝ)⁻¹
  ((1-z) * ∏ p ∈ S, (1 + z^p.natDegree)⁻¹) *
    ∑' k : ℕ, ((greedyPrimeAvoidingLayer S k).card : ℝ) * z^(3*k)

theorem summable_greedyPrimeAvoiding_cubeWeight (S : Finset F[X]) :
    Summable (fun k : ℕ ↦ ((greedyPrimeAvoidingLayer S k).card : ℝ) *
      (Fintype.card F : ℝ)⁻¹^(3*k)) := by
  let q := (Fintype.card F : ℝ)
  let z := q⁻¹
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hz₀ : 0 ≤ z := inv_nonneg.mpr hq₀.le
  have hz₁ : z < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeom : Summable (fun k : ℕ ↦ z^(2*k)) := by
    simpa only [pow_mul] using
      summable_geometric_of_lt_one (pow_nonneg hz₀ 2) (pow_lt_one₀ hz₀ hz₁ (by decide : 2 ≠ 0))
  change Summable (fun k : ℕ ↦ ((greedyPrimeAvoidingLayer S k).card : ℝ)*z^(3*k))
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_) hgeom
  have hcard : ((greedyPrimeAvoidingLayer S k).card : ℝ) ≤ q^k := by
    dsimp [q]
    exact_mod_cast card_greedyPrimeAvoidingLayer_le S k
  calc
    _ ≤ q^k*z^(3*k) := mul_le_mul_of_nonneg_right hcard (pow_nonneg hz₀ _)
    _ = z^(2*k) := by
      rw [show 3*k = k+2*k by omega, pow_add, ← mul_assoc]
      have hcancel : q^k*z^k = 1 := by
        rw [show z = q⁻¹ by rfl, ← mul_pow, mul_inv_cancel₀ hq₀.ne', one_pow]
      rw [hcancel, one_mul]

private theorem tendsto_cube_weighted_convolution
    (w : ℕ → ℝ) (hws : Summable w) (hw : ∀ t, 0 ≤ w t)
    {r : ℕ → ℝ} {c : ℝ} (hr : ∀ n, r n ∈ Set.Icc 0 1)
    (hR : Tendsto r atTop (𝓝 c)) :
    Tendsto (fun N ↦ ∑ t ∈ Finset.range (N/3+1), r (N-3*t)*w t) atTop
      (𝓝 (c * ∑' t : ℕ, w t)) := by
  let a (N t : ℕ) := if 3*t ≤ N then r (N-3*t)*w t else 0
  have hpoint (t : ℕ) : Tendsto (a · t) atTop (𝓝 (c*w t)) := by
    refine ((hR.comp (tendsto_sub_atTop_nat (3*t))).mul tendsto_const_nhds).congr' ?_
    filter_upwards [eventually_ge_atTop (3*t)] with N hN
    exact (if_pos hN).symm
  have hbound (N t : ℕ) : ‖a N t‖ ≤ w t := by
    by_cases h : 3*t ≤ N
    · simp only [a, if_pos h, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hr _).1 (hw t))]
      exact mul_le_of_le_one_left (hw t) (hr _).2
    · simpa only [a, if_neg h, norm_zero] using hw t
  have hlimit := tendsto_tsum_of_dominated_convergence hws hpoint (Eventually.of_forall hbound)
  have hfinite (N : ℕ) : (∑' t, a N t) = ∑ t ∈ Finset.range (N/3+1), r (N-3*t)*w t := by
    rw [tsum_eq_sum (s := Finset.range (N/3+1))]
    · apply Finset.sum_congr rfl
      intro t ht
      have := Finset.mem_range.mp ht
      exact if_pos (by omega)
    · intro t ht
      rw [Finset.mem_range] at ht
      exact if_neg (by omega)
  simpa only [hfinite, tsum_mul_left] using hlimit

/-- The actual normalized cofactor counts converge for any finite set of
excluded monic primes. -/
theorem tendsto_greedyPrimeAvoidingLayer_card_div_pow (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    Tendsto (fun n ↦ ((greedyPrimeAvoidingLayer S n).card : ℝ) / (Fintype.card F : ℝ)^n)
      atTop (𝓝 (greedyPrimeAvoidingDensity S)) := by
  let q := (Fintype.card F : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  let r (n : ℕ) := ((squarefreeLayer F S n).card : ℝ)/q^n
  let w (k : ℕ) := ((greedyPrimeAvoidingLayer S k).card : ℝ)*q⁻¹^(3*k)
  have hr (n : ℕ) : r n ∈ Set.Icc 0 1 := by
    refine ⟨by dsimp [r]; positivity, (div_le_one (pow_pos hq _)).mpr ?_⟩
    have hcard : (squarefreeLayer F S n).card ≤ Fintype.card F ^ n := by
      rw [← card_monicLayer (F := F)]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    dsimp [q]
    exact_mod_cast hcard
  have ht := tendsto_cube_weighted_convolution w (summable_greedyPrimeAvoiding_cubeWeight S)
    (fun _ ↦ by dsimp [w]; positivity) hr (tendsto_normalized_squarefreeLayer S hS)
  refine ht.congr (fun n ↦ ?_)
  symm
  change ((greedyPrimeAvoidingLayer S n).card : ℝ)/q^n = _
  rw [card_greedyPrimeAvoidingLayer S hS n, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  have hsplit : n = (n-3*k)+(3*k) := by omega
  have hpow : q^n = q^(n-3*k)*q^(3*k) :=
    (congrArg (fun i : ℕ ↦ q^i) hsplit).trans (pow_add q _ _)
  simp only [Nat.cast_mul, r, w, div_eq_mul_inv, inv_pow]
  rw [hpow, mul_inv]
  ring

/-- Applying the squarefree restriction at all remaining primes gives a
lower bound on the normalized greedy cofactor density. -/
theorem greedyPrimeAvoidingDensity_ge_squarefree (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    let z := (Fintype.card F : ℝ)⁻¹
    (1-z) * (∏ p ∈ S, (1+z^p.natDegree)⁻¹) ≤ greedyPrimeAvoidingDensity S := by
  let z := (Fintype.card F : ℝ)⁻¹
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hq : 1 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hz₁ : z < 1 := inv_lt_one_of_one_lt₀ hq
  let w (k : ℕ) := ((greedyPrimeAvoidingLayer S k).card : ℝ)*z^(3*k)
  have hsum : (1 : ℝ) ≤ ∑' k, w k := by
    have hzero := (summable_greedyPrimeAvoiding_cubeWeight S).sum_le_tsum
      ({0} : Finset ℕ) fun _ _ ↦ by positivity
    simpa [z,w,card_greedyPrimeAvoidingLayer_zero S hS] using hzero
  change (1-z) * (∏ p ∈ S, (1+z^p.natDegree)⁻¹) ≤
    ((1-z) * ∏ p ∈ S, (1+z^p.natDegree)⁻¹) * _
  exact le_mul_of_one_le_right (mul_nonneg (sub_nonneg.mpr hz₁.le)
    (Finset.prod_nonneg fun _ _ ↦ by positivity)) hsum

/-- The lower bound on the exterior greedy coefficient after accounting
for exclusion of the finitely many distinguished primes. -/
theorem greedyPrimeAvoidingDensity_ge_exclusion_product (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    let z := (Fintype.card F : ℝ)⁻¹
    (1-z) * (∏ p ∈ S, (1-z^p.natDegree)) ≤ greedyPrimeAvoidingDensity S := by
  let z := (Fintype.card F : ℝ)⁻¹
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hq : 1 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hz₁ : z < 1 := inv_lt_one_of_one_lt₀ hq
  refine (mul_le_mul_of_nonneg_left (Finset.prod_le_prod ?_ ?_) (sub_nonneg.mpr hz₁.le)).trans
    (greedyPrimeAvoidingDensity_ge_squarefree S hS)
  · intro p _
    exact sub_nonneg.mpr (pow_le_one₀ hz hz₁.le)
  · intro p _
    change 1-z^p.natDegree ≤ (1+z^p.natDegree)⁻¹
    rw [inv_eq_one_div (1+z^p.natDegree),
      le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (pow_nonneg hz _))]
    nlinarith [sq_nonneg (z^p.natDegree)]

end GRHArticle.ProgressionFree
