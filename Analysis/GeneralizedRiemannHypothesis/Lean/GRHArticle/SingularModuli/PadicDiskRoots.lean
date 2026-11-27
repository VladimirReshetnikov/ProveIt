import GRHArticle.SingularModuli.PadicCutoff
import GRHArticle.SingularModuli.PadicDiskBijection
import GRHArticle.SingularModuli.PadicScaling
import GRHArticle.SingularModuli.SevenAdicCutoff
import GRHArticle.SingularModuli.WeightCutoff
import Mathlib.Data.Finset.Sort

/-!
# Distinct roots of sparse polynomials in a multiplicative p-adic disk

The bound in `smd:lem:disk` transfers Strassmann's result from the closed unit
ball to the multiplicative disk using the p-adic exponential.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- A cutoff on the factorial weights bounds the number of distinct roots of a
sparse polynomial in the multiplicative disk at depth `r`. -/
theorem encard_sparseDiskRoots_le_of_weight_cutoff {t N : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a : ℂ_[p]) {r : ℚ}
    (hn : Function.Injective n) (hc : c ≠ 0) (ha : a ≠ 0)
    (hr : 1 / ((p : ℚ) - 1) < r)
    (hcut : ∀ k > N, ∀ j : Fin t, factorialWeight p r j < factorialWeight p r k) :
    {x : ℂ_[p] | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧
      (∑ i, c i * x ^ n i) = 0}.encard ≤ N := by
  obtain ⟨b, hb⟩ := exists_norm_eq_rpow_neg_depth (p := p) r
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hb0 : b ≠ 0 := norm_pos_iff.mp (by
    rw [hb]
    exact Real.rpow_pos_of_pos hp0 _)
  have hr' : 1 / ((p : ℝ) - 1) < (r : ℝ) := by exact_mod_cast hr
  have hratio := geometric_ratio_lt_one_of_depth b r hr' hb
  let seriesRoots : Set ℂ_[p] :=
    {y | ‖y‖ ≤ 1 ∧ seriesValue (exponentialCoefficient n c a b) y = 0}
  let f (y : ℂ_[p]) := a * NormedSpace.exp (b * y)
  have hsub : {x : ℂ_[p] | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧
      (∑ i, c i * x ^ n i) = 0} ⊆ f '' seriesRoots := by
    intro x hx
    have hdisc : ‖x / a - 1‖ ≤ ‖b‖ := hb.symm ▸ hx.1
    obtain ⟨y, hy, heq⟩ := (expSubstitution_bijOn_unitBall a b ha hb0 hratio).surjOn hdisc
    refine ⟨y, ⟨hy, ?_⟩, heq⟩
    change a * NormedSpace.exp (b * y) = x at heq
    rw [seriesValue, ← exp_substitution_eq_tsum n c a b y hratio hy, heq]
    exact hx.2
  exact (Set.encard_mono hsub).trans ((Set.encard_image_le f seriesRoots).trans
    (encard_exponentialSeriesRoots_le_of_weight_cutoff n c a hn hc ha hr' hb hcut))

/-- The maximum in the article's definition of `B_p(t,r)`. -/
noncomputable def sparseDiskRootBound (p t : ℕ) [Fact (Nat.Prime p)] (r : ℚ)
    (ht : 0 < t) (hr : 1 / ((p : ℚ) - 1) < r) : ℕ := by
  classical
  exact Nat.find (exists_greatest_factorialWeightIndex ht hr)

theorem isGreatest_sparseDiskRootBound {t : ℕ} {r : ℚ}
    (ht : 0 < t) (hr : 1 / ((p : ℚ) - 1) < r) :
    IsGreatest {k : ℕ | ∃ i : Fin t, factorialWeight p r k ≤ factorialWeight p r i}
      (sparseDiskRootBound p t r ht hr) := by
  classical
  exact Nat.find_spec (exists_greatest_factorialWeightIndex ht hr)

/-- The local root count in `smd:lem:disk`, with the maximum of the stated
factorial weights as its bound. -/
theorem encard_sparseDiskRoots_le {t : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a : ℂ_[p]) {r : ℚ}
    (ht : 0 < t) (hn : Function.Injective n) (hc : c ≠ 0) (ha : a ≠ 0)
    (hr : 1 / ((p : ℚ) - 1) < r) :
    {x : ℂ_[p] | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧
      (∑ i, c i * x ^ n i) = 0}.encard ≤ sparseDiskRootBound p t r ht hr := by
  apply encard_sparseDiskRoots_le_of_weight_cutoff n c a hn hc ha hr
  intro k hk j
  exact factorialWeight_lt_of_gt_greatest (isGreatest_sparseDiskRootBound ht hr) hk j

/-- The disk bound applies to a polynomial with its actual number of nonzero
coefficients, without a chosen enumeration of the terms. -/
theorem encard_polynomialDiskRoots_le (P : Polynomial ℂ_[p]) (hP : P ≠ 0)
    (a : ℂ_[p]) (ha : a ≠ 0) {r : ℚ} (hr : 1 / ((p : ℚ) - 1) < r) :
    {x : ℂ_[p] | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧ P.eval x = 0}.encard ≤
      sparseDiskRootBound p P.support.card r
        (Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)) hr := by
  have ht : 0 < P.support.card := Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
  let e := P.support.orderEmbOfFin rfl
  let c (i : Fin P.support.card) := P.coeff (e i)
  have hc : c ≠ 0 := by
    intro hz
    let i : Fin P.support.card := ⟨0, ht⟩
    exact (Polynomial.mem_support_iff.mp (P.support.orderEmbOfFin_mem rfl i)) (congrFun hz i)
  have hsum (x : ℂ_[p]) : (∑ i, c i * x ^ e i) = P.eval x := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    conv_rhs => rw [← P.support.map_orderEmbOfFin_univ (k := P.support.card) rfl]
    rw [Finset.sum_map]
    rfl
  simpa only [hsum] using encard_sparseDiskRoots_le e c a ht e.injective hc ha hr

/-- The depth-half disk bound at seven used in the trinomial argument. -/
theorem encard_sparseTrinomialRoots_in_seven_half_disk_le_two [Fact (Nat.Prime 7)]
    (n : Fin 3 → ℕ) (c : Fin 3 → ℂ_[7]) (a : ℂ_[7])
    (hn : Function.Injective n) (hc : c ≠ 0) (ha : a ≠ 0) :
    {x : ℂ_[7] | ‖x / a - 1‖ ≤ (7 : ℝ) ^ (-(1 / 2 : ℚ) : ℝ) ∧
      (∑ i, c i * x ^ n i) = 0}.encard ≤ 2 := by
  apply encard_sparseDiskRoots_le_of_weight_cutoff (p := 7) (r := 1 / 2) n c a hn hc ha
    (by norm_num)
  intro k hk j
  apply lt_of_not_ge
  intro h
  exact (not_le_of_gt hk) (seven_half_trinomial_cutoff.2 ⟨j, j.isLt, h⟩)

end GRHArticle.SingularModuli
