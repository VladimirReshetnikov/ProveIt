import GRHArticle.SingularModuli.PadicDiskRoots
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Root counts at the sparse-polynomial depth thresholds

This is the polynomial root-count formulation of `smd:cor:threshold`.
Open disks encode strict valuation depth, even when the bound is stated in
terms of the p-adic norm.
-/

namespace GRHArticle.SingularModuli

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

omit hp in
private theorem weight_lt_of_lt_term_le_tail {r : ℚ} {t : ℕ}
    (hstep : ∀ i < t, ∀ d > 0, factorialWeight p r i < factorialWeight p r (i + d))
    {i k : ℕ} (hi : i < t) (hk : t ≤ k) : factorialWeight p r i < factorialWeight p r k := by
  simpa only [Nat.add_sub_of_le (hi.le.trans hk)] using hstep i hi (k - i) (by omega)

private theorem encard_polynomialDiskRoots_le_of_weight_tail {t : ℕ} {r : ℚ}
    (P : Polynomial ℂ_[p]) (hP : P ≠ 0) (a : ℂ_[p]) (ha : a ≠ 0) (hs : P.support.card ≤ t)
    (hr : 1 / ((p : ℚ) - 1) < r)
    (hcut : ∀ i < t, ∀ k ≥ t, factorialWeight p r i < factorialWeight p r k) :
    {x : ℂ_[p] | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧ P.eval x = 0}.encard ≤ ((t - 1 : ℕ) : ℕ∞) := by
  have hsupport : 0 < P.support.card :=
    Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
  have hbound : sparseDiskRootBound p P.support.card r hsupport hr ≤ t - 1 := by
    by_contra! h
    obtain ⟨i, hi⟩ := (isGreatest_sparseDiskRootBound hsupport hr).1
    exact (not_le_of_gt (hcut i (i.isLt.trans_le hs) _ (by omega))) hi
  exact (encard_polynomialDiskRoots_le P hP a ha hr).trans (by exact_mod_cast hbound)

private theorem exists_rat_depth_of_lt_rpow {q u : ℝ} (hq : 1 < q) (hu : 0 ≤ u) (κ : ℚ)
    (h : u < q ^ (-(κ : ℝ))) :
    ∃ r : ℚ, κ < r ∧ u ≤ q ^ (-(r : ℝ)) := by
  have hq₀ : 0 < q := zero_lt_one.trans hq
  by_cases hu₀ : u = 0
  · exact ⟨κ + 1, by linarith, hu₀ ▸ Real.rpow_nonneg hq₀.le _⟩
  have hu_pos := lt_of_le_of_ne hu (Ne.symm hu₀)
  have hlog := Real.logb_lt_logb hq hu_pos h
  rw [Real.logb_rpow hq₀ hq.ne'] at hlog
  have hκu : (κ : ℝ) < -Real.logb q u := by linarith only [hlog]
  obtain ⟨r, hκr, hru⟩ := exists_rat_btwn hκu
  refine ⟨r, by exact_mod_cast hκr, ?_⟩
  rw [← Real.rpow_logb hq₀ hq.ne' hu_pos]
  exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith only [hru])

private theorem encard_polynomialDiskRoots_lt_of_weight_tail {t : ℕ} {κ : ℚ}
    (P : Polynomial ℂ_[p]) (hP : P ≠ 0) (a : ℂ_[p]) (ha : a ≠ 0) (hs : P.support.card ≤ t)
    (hκ : 1 / ((p : ℚ) - 1) ≤ κ)
    (hcut : ∀ r > κ, ∀ i < t, ∀ k ≥ t, factorialWeight p r i < factorialWeight p r k) :
    {x : ℂ_[p] | ‖x / a - 1‖ < (p : ℝ) ^ (-(κ : ℝ)) ∧ P.eval x = 0}.encard ≤ ((t - 1 : ℕ) : ℕ∞) := by
  let Z : Set ℂ_[p] := {x | ‖x / a - 1‖ < (p : ℝ) ^ (-(κ : ℝ)) ∧ P.eval x = 0}
  change Z.encard ≤ ((t - 1 : ℕ) : ℕ∞)
  have hsupport : 0 < P.support.card :=
    Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
  have ht : 0 < t := hsupport.trans_le hs
  apply le_of_not_gt
  intro h
  have htZ : (t : ℕ∞) ≤ Z.encard := by
    have ht₁ : t - 1 + 1 = t := by omega
    have hcast : ((t - 1 : ℕ) : ℕ∞) + 1 = (t : ℕ∞) := by exact_mod_cast ht₁
    exact hcast ▸ ENat.coe_add_one_le_iff.mpr h
  obtain ⟨S, hSZ, hScard⟩ := Set.exists_subset_encard_eq htZ
  have hSf := Set.finite_of_encard_eq_coe hScard
  have hS_card : hSf.toFinset.card = t := by
    rw [hSf.encard_eq_coe_toFinset_card] at hScard
    exact_mod_cast hScard
  have hS_ne : hSf.toFinset.Nonempty := Finset.card_pos.mp (hS_card ▸ ht)
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image hSf.toFinset (fun x ↦ ‖x / a - 1‖) hS_ne
  have hxZ := hSZ (hSf.mem_toFinset.mp hx)
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨r, hκr, hxr⟩ := exists_rat_depth_of_lt_rpow hp₁ (norm_nonneg _) κ hxZ.1
  have hsub : S ⊆
      {y : ℂ_[p] | ‖y / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧ P.eval y = 0} :=
    fun y hy ↦ ⟨(hmax y (hSf.mem_toFinset.mpr hy)).trans hxr, (hSZ hy).2⟩
  have hc := (Set.encard_mono hsub).trans
    (encard_polynomialDiskRoots_le_of_weight_tail P hP a ha hs (hκ.trans_lt hκr) (hcut r hκr))
  rw [hScard] at hc
  have hnat : t ≤ t - 1 := by exact_mod_cast hc
  omega

/-- A polynomial of at most `t` terms has fewer than `t` roots at relative
depth strictly greater than an admissible interval threshold `κ`. -/
theorem encard_polynomialDiskRoots_lt_of_interval_bound {t : ℕ} {κ : ℚ}
    (P : Polynomial ℂ_[p]) (hP : P ≠ 0) (a : ℂ_[p]) (ha : a ≠ 0) (hs : P.support.card ≤ t)
    (hκ : 1 / ((p : ℚ) - 1) ≤ κ)
    (hval : ∀ i < t, ∀ d > 0, (factorialIntervalValuation p i d : ℚ) ≤ (d : ℚ) * κ) :
    {x : ℂ_[p] | ‖x / a - 1‖ < (p : ℝ) ^ (-(κ : ℝ)) ∧ P.eval x = 0}.encard ≤ ((t - 1 : ℕ) : ℕ∞) := by
  apply encard_polynomialDiskRoots_lt_of_weight_tail P hP a ha hs hκ
  intro r hr i hi k hk
  exact weight_lt_of_lt_term_le_tail
    (fun j hj d hd ↦ factorialWeight_lt_add_of_bound (hval j hj d hd) hr hd) hi hk

/-- The depth threshold `1/(p-t+1)` for a prime `p ≥ t`. -/
theorem encard_polynomialDiskRoots_lt_prime_ge_terms {t : ℕ} (ht : 2 ≤ t) (htp : t ≤ p)
    (P : Polynomial ℂ_[p]) (hP : P ≠ 0) (a : ℂ_[p]) (ha : a ≠ 0) (hs : P.support.card ≤ t) :
    {x : ℂ_[p] | ‖x / a - 1‖ < (p : ℝ) ^ (-((1 / ((p - t + 1 : ℕ) : ℚ) : ℚ) : ℝ)) ∧
      P.eval x = 0}.encard ≤ ((t - 1 : ℕ) : ℕ∞) := by
  have hsub : ((p - t + 1 : ℕ) : ℚ) ≤ (p : ℚ) - 1 := by
    have hnat : p - t + 1 ≤ p - 1 := by omega
    have hcast : ((p - t + 1 : ℕ) : ℚ) ≤ ((p - 1 : ℕ) : ℚ) := by exact_mod_cast hnat
    simpa only [Nat.cast_sub hp.out.one_lt.le, Nat.cast_one] using hcast
  have hκ : 1 / ((p : ℚ) - 1) ≤ 1 / ((p - t + 1 : ℕ) : ℚ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr (by omega)) hsub
  apply encard_polynomialDiskRoots_lt_of_weight_tail P hP a ha hs hκ
  intro r hr i hi k hk
  exact weight_lt_of_lt_term_le_tail
    (fun j hj d hd ↦ factorialWeight_lt_add_of_prime_ge_terms ht htp hj hd hr) hi hk

/-- At `p = 2` the threshold is two for polynomials of at most five terms. -/
theorem encard_polynomialDiskRoots_lt_two [Fact (Nat.Prime 2)] {t : ℕ} (ht : t ≤ 5)
    (P : Polynomial ℂ_[2]) (hP : P ≠ 0) (a : ℂ_[2]) (ha : a ≠ 0) (hs : P.support.card ≤ t) :
    {x : ℂ_[2] | ‖x / a - 1‖ < (2 : ℝ) ^ (-((2 : ℚ) : ℝ)) ∧ P.eval x = 0}.encard
      ≤ ((t - 1 : ℕ) : ℕ∞) := by
  apply encard_polynomialDiskRoots_lt_of_weight_tail (κ := 2) P hP a ha hs (by norm_num)
  intro r hr i hi k hk
  exact weight_lt_of_lt_term_le_tail
    (fun j hj d hd ↦ factorialWeight_two_lt_add (hj.trans_le ht) hd hr) hi hk

/-- At `p = 3` the threshold is one for polynomials of at most five terms. -/
theorem encard_polynomialDiskRoots_lt_three [Fact (Nat.Prime 3)] {t : ℕ} (ht : t ≤ 5)
    (P : Polynomial ℂ_[3]) (hP : P ≠ 0) (a : ℂ_[3]) (ha : a ≠ 0) (hs : P.support.card ≤ t) :
    {x : ℂ_[3] | ‖x / a - 1‖ < (3 : ℝ) ^ (-((1 : ℚ) : ℝ)) ∧ P.eval x = 0}.encard
      ≤ ((t - 1 : ℕ) : ℕ∞) := by
  apply encard_polynomialDiskRoots_lt_of_weight_tail (κ := 1) P hP a ha hs (by norm_num)
  intro r hr i hi k hk
  exact weight_lt_of_lt_term_le_tail
    (fun j hj d hd ↦ factorialWeight_three_lt_add (hj.trans_le ht) hd hr) hi hk

/-- The closed depth-half disk at seven has at most two zeros of a nonzero
polynomial with at most three nonzero coefficients. -/
theorem encard_polynomialDiskRoots_seven_half_le_two [Fact (Nat.Prime 7)]
    (P : Polynomial ℂ_[7]) (hP : P ≠ 0) (a : ℂ_[7]) (ha : a ≠ 0) (hs : P.support.card ≤ 3) :
    {x : ℂ_[7] | ‖x / a - 1‖ ≤ (7 : ℝ) ^ (-((1 / 2 : ℚ) : ℝ)) ∧ P.eval x = 0}.encard ≤ 2 := by
  apply encard_polynomialDiskRoots_le_of_weight_tail (p := 7) (t := 3) (r := 1/2)
    P hP a ha hs (by norm_num)
  intro i hi k hk
  exact weight_lt_of_lt_term_le_tail
    (fun j hj d hd ↦ factorialWeight_lt_add_of_prime_ge_terms
      (by norm_num : 2 ≤ 3) (by norm_num : 3 ≤ 7) hj hd (by norm_num)) hi hk

/-- A nonzero polynomial of at most `t` terms fails to vanish at one of any
`t` distinct points of relative depth strictly greater than `κ`. -/
theorem exists_eval_ne_zero_of_depth_threshold {t : ℕ} {κ : ℚ}
    (P : Polynomial ℂ_[p]) (hP : P ≠ 0) (a : ℂ_[p]) (ha : a ≠ 0) (hs : P.support.card ≤ t)
    (hκ : 1 / ((p : ℚ) - 1) ≤ κ)
    (hval : ∀ i < t, ∀ d > 0, (factorialIntervalValuation p i d : ℚ) ≤ (d : ℚ) * κ)
    (z : Fin t → ℂ_[p]) (hz : Function.Injective z)
    (hzdepth : ∀ i, ‖z i / a - 1‖ < (p : ℝ) ^ (-(κ : ℝ))) :
    ∃ i, P.eval (z i) ≠ 0 := by
  classical
  by_contra! hzroot
  let S := Finset.univ.image z
  have hS : S.card = t := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hz]
    exact Fintype.card_fin t
  have hsub : (S : Set ℂ_[p]) ⊆
      {x : ℂ_[p] | ‖x / a - 1‖ < (p : ℝ) ^ (-(κ : ℝ)) ∧ P.eval x = 0} := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hzdepth i, hzroot i⟩
  have hbound := (Set.encard_mono hsub).trans
    (encard_polynomialDiskRoots_lt_of_interval_bound P hP a ha hs hκ hval)
  rw [Set.encard_coe_eq_coe_finsetCard, hS] at hbound
  have hnat : t ≤ t - 1 := by exact_mod_cast hbound
  have hsupport : 0 < P.support.card :=
    Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
  omega

/-- The generalized Vandermonde determinant in the article's depth-threshold
corollary is nonzero. -/
theorem det_pow_ne_zero_of_depth_threshold {t : ℕ} {κ : ℚ}
    (a : ℂ_[p]) (ha : a ≠ 0) (hκ : 1 / ((p : ℚ) - 1) ≤ κ)
    (hval : ∀ i < t, ∀ d > 0, (factorialIntervalValuation p i d : ℚ) ≤ (d : ℚ) * κ)
    (n : Fin t → ℕ) (hn : Function.Injective n) (z : Fin t → ℂ_[p]) (hz : Function.Injective z)
    (hzdepth : ∀ i, ‖z i / a - 1‖ < (p : ℝ) ^ (-(κ : ℝ))) :
    (Matrix.of fun i j : Fin t ↦ z i ^ n j).det ≠ 0 := by
  classical
  let M := Matrix.of fun i j : Fin t ↦ z i ^ n j
  change M.det ≠ 0
  have hinj : Function.Injective M.mulVec := by
    intro c d hcd
    by_contra! hne
    let e := c - d
    have he : e ≠ 0 := sub_ne_zero.mpr hne
    have hzero : M.mulVec e = 0 := by simp only [e, Matrix.mulVec_sub, hcd, sub_self]
    let P : Polynomial ℂ_[p] := ∑ j, Polynomial.monomial (n j) (e j)
    have hcoeff (j : Fin t) : P.coeff (n j) = e j := by
      dsimp only [P]
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
      · exact Polynomial.coeff_monomial_same (n j) (e j)
      · intro k _ hkj
        simp [Polynomial.coeff_monomial, hn.ne hkj]
      · simp
    have hP : P ≠ 0 := by
      intro h
      apply he
      funext j
      simpa [h] using (hcoeff j).symm
    have hsub : P.support ⊆ Finset.univ.image n := by
      intro k hk
      by_contra! hkn
      have hk₀ : P.coeff k = 0 := by
        dsimp only [P]
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro j hj
        have hnj : n j ≠ k := fun h ↦ hkn (Finset.mem_image.mpr ⟨j, hj, h⟩)
        simp [Polynomial.coeff_monomial, hnj]
      exact (Polynomial.mem_support_iff.mp hk) hk₀
    have hs : P.support.card ≤ t :=
      (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (Fintype.card_fin t).le)
    obtain ⟨i, hi⟩ := exists_eval_ne_zero_of_depth_threshold P hP a ha hs hκ hval z hz hzdepth
    apply hi
    simpa only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, M, Matrix.mulVec,
      Matrix.of_apply, dotProduct, Pi.zero_apply, mul_comm] using congrFun hzero i
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

end GRHArticle.SingularModuli
