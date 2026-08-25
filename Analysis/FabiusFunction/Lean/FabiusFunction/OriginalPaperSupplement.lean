import FabiusFunction.AnalyticMoments
import FabiusFunction.ExactInversePower
import FabiusFunction.FourierProduct
import FabiusFunction.GlobalExtension
import FabiusFunction.GlobalDyadic
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Further statements from the original paper on Rvachev's function

This file packages Theorems 4, 6, and 7 of arXiv:1702.05442 in the
notation used by this development.  It also records the finite Taylor
expansion at dyadic points and the paper's unnumbered corollary that
Rvachev's compactly supported function is not real analytic at any point of
its support.  The exact even and odd integer values of the signed global
extension make the dyadic derivative truncation transparent.
-/

open scoped BigOperators ContDiff Topology
open Filter Finset Set

namespace Fabius

set_option autoImplicit false

noncomputable section

/-! ## Theorem 4 and equations (21)--(23) -/

/-- The function called `theta` in Theorem 4 is the signed global Fabius
extension. -/
abbrev paperTheta (F : BoundedFabius) : ℝ → ℝ := extendedFabius F

/-- Theorem 4(a): `theta` is infinitely differentiable. -/
theorem original_theorem_four_a
    (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℝ ∞ (paperTheta F) :=
  extendedFabius_contDiff F hF

/-- Theorem 4(b), equation (21): `theta'(t) = 2 theta(2t)`. -/
theorem original_theorem_four_b
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    HasDerivAt (paperTheta F) (2 * paperTheta F (2 * t)) t :=
  extendedFabius_hasDerivAt F hF t

/-- Equation (22), obtained by repeatedly differentiating equation (21). -/
theorem paperTheta_iteratedDeriv
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (paperTheta F) t =
      2 ^ (k + 1).choose 2 * paperTheta F (2 ^ k * t) :=
  iteratedDeriv_extendedFabius F hF k t

/-- Theorem 4(c), equation (23): the derivatives of `up` on its support
are values of the signed global extension. -/
theorem original_theorem_four_c
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    iteratedDeriv k (rvachevUp F) t =
      2 ^ (k + 1).choose 2 * paperTheta F (2 ^ k * t + 2 ^ k) := by
  rw [iteratedDeriv_rvachev F hF k t ht]
  congr 1
  ring

/-! ## The alternate cosine product in equation (9) -/

/-- The ordered partial products in the first alternate product of equation
(9).  Index `m` here represents the paper's index `m+1`. -/
noncomputable def rvachevCosinePartialProduct (z : ℂ) (N : ℕ) : ℂ :=
  ∏ m ∈ range N,
    Complex.cos (Real.pi * z / (2 : ℂ) ^ (m + 1)) ^ (m + 1)

/-- The first alternate infinite product in equation (9), defined as the
limit of its naturally ordered partial products. -/
noncomputable def rvachevCosineProduct (z : ℂ) : ℂ :=
  Filter.limUnder atTop (rvachevCosinePartialProduct z)

private lemma sincPartial_eq_cosinePartial_mul_tail
    (z : ℂ) (N : ℕ) :
    (∏ h ∈ range N, complexSinc (Real.pi * z / (2 : ℂ) ^ h)) =
      rvachevCosinePartialProduct z N *
        complexSinc (Real.pi * z / (2 : ℂ) ^ N) ^ N := by
  induction N with
  | zero => simp [rvachevCosinePartialProduct]
  | succ N ih =>
      rw [prod_range_succ, ih]
      simp only [rvachevCosinePartialProduct]
      rw [prod_range_succ]
      have harg :
          (Real.pi : ℂ) * z / 2 ^ N / 2 =
            Real.pi * z / 2 ^ (N + 1) := by
        rw [pow_succ]
        ring
      have htail :
          complexSinc (Real.pi * z / (2 : ℂ) ^ N) =
            Complex.cos (Real.pi * z / (2 : ℂ) ^ (N + 1)) *
              complexSinc (Real.pi * z / (2 : ℂ) ^ (N + 1)) := by
        rw [complexSinc_eq_cos_mul, harg]
      rw [mul_assoc, ← pow_succ, htail, mul_pow]
      ring

private lemma tendsto_sinc_dyadic_tail_pow_one (z : ℂ) :
    Tendsto (fun N : ℕ ↦ complexSinc (Real.pi * z / (2 : ℂ) ^ N) ^ N)
      atTop (nhds 1) := by
  let a : ℕ → ℂ := fun N ↦ (Real.pi : ℂ) * z / (2 : ℂ) ^ N
  have ha : Tendsto a atTop (nhds 0) := by
    have hpow : Tendsto (fun N : ℕ ↦ ((2 : ℂ)⁻¹) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    simpa [a, div_eq_mul_inv, inv_pow] using hpow.const_mul ((Real.pi : ℂ) * z)
  have hO : (fun N : ℕ ↦ complexSinc (a N) - 1) =O[atTop] a := by
    simpa [Function.comp_def] using complexSinc_sub_one_isBigO.comp_tendsto ha
  have hOmul :
      (fun N : ℕ ↦ (N : ℂ) * (complexSinc (a N) - 1)) =O[atTop]
        (fun N : ℕ ↦ (N : ℂ) * a N) :=
    (Asymptotics.isBigO_refl (fun N : ℕ ↦ (N : ℂ)) atTop).mul hO
  have hreal : Tendsto (fun N : ℕ ↦ (N : ℝ) * (1 / 2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one (by norm_num)
  have hcomplex : Tendsto
      (Complex.ofReal ∘ fun N : ℕ ↦ (N : ℝ) * (1 / 2 : ℝ) ^ N)
      atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hcompare : Tendsto (fun N : ℕ ↦ (N : ℂ) * a N) atTop (nhds 0) := by
    have h := hcomplex.const_mul ((Real.pi : ℂ) * z)
    convert h using 1
    · funext N
      have hcast :
          (((N : ℝ) * (1 / 2 : ℝ) ^ N : ℝ) : ℂ) =
            (N : ℂ) * ((2 : ℂ) ^ N)⁻¹ := by
        push_cast
        rw [one_div, inv_pow]
      dsimp [a]
      rw [hcast]
      simp only [div_eq_mul_inv]
      ring
    · simp
  have hg : Tendsto
      (fun N : ℕ ↦ (N : ℂ) * (complexSinc (a N) - 1))
      atTop (nhds 0) := hOmul.trans_tendsto hcompare
  have hpow := Complex.tendsto_one_add_pow_exp_of_tendsto hg
  simpa [a] using hpow

/-- The first equality of equation (9), in ordered-partial-product form. -/
theorem tendsto_rvachevCosinePartialProduct
    (z : ℂ) :
    Tendsto (rvachevCosinePartialProduct z) atTop
      (nhds (rvachevFourierProduct z)) := by
  have hsinc : Tendsto
      (fun N : ℕ ↦ ∏ h ∈ range N,
        complexSinc (Real.pi * z / (2 : ℂ) ^ h))
      atTop (nhds (rvachevFourierProduct z)) := by
    simpa [rvachevFourierProduct] using
      (sincFactors_multipliable z).tendsto_prod_tprod_nat
  have htail := tendsto_sinc_dyadic_tail_pow_one z
  have hquot := hsinc.div htail (by norm_num : (1 : ℂ) ≠ 0)
  have hquot' : Tendsto
      ((fun N : ℕ ↦ ∏ h ∈ range N,
          complexSinc (Real.pi * z / (2 : ℂ) ^ h)) /
        fun N : ℕ ↦ complexSinc (Real.pi * z / (2 : ℂ) ^ N) ^ N)
      atTop (nhds (rvachevFourierProduct z)) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [htail.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with N hN
  change (∏ h ∈ range N,
      complexSinc (Real.pi * z / (2 : ℂ) ^ h)) /
        complexSinc (Real.pi * z / (2 : ℂ) ^ N) ^ N =
      rvachevCosinePartialProduct z N
  rw [sincPartial_eq_cosinePartial_mul_tail z N]
  field_simp

/-- Equation (9), first product: the sinc and weighted-cosine products agree. -/
theorem rvachevFourierProduct_eq_cosineProduct (z : ℂ) :
    rvachevFourierProduct z = rvachevCosineProduct z := by
  rw [rvachevCosineProduct]
  exact (tendsto_rvachevCosinePartialProduct z).limUnder_eq.symm

/-! ## Dyadic Taylor expansions (equation (24)) -/

/-- The signed global extension vanishes at every even nonnegative integer. -/
theorem paperTheta_even_nat_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (b : ℕ) :
    paperTheta F (2 * (b : ℝ)) = 0 := by
  change extendedFabius F (2 * (b : ℝ)) = 0
  rw [extendedFabius_eq_single_translate F hF b le_rfl (by norm_num)]
  rw [show 2 * (b : ℝ) - 2 * (b : ℝ) - 1 = -1 by ring,
    rvachevUp_eq_zero_of_le_neg_one F hF le_rfl, mul_zero]

/-- Exact value of the signed global extension at every odd nonnegative
integer. -/
theorem paperTheta_odd_nat_eq
    (F : BoundedFabius) (hF : IsFabius F) (b : ℕ) :
    paperTheta F (2 * (b : ℝ) + 1) = (-1 : ℝ) ^ binaryWeight b := by
  change extendedFabius F (2 * (b : ℝ) + 1) = _
  rw [extendedFabius_eq_single_translate F hF b (by norm_num) (by norm_num),
    show 2 * (b : ℝ) + 1 - 2 * (b : ℝ) - 1 = 0 by ring,
    rvachevUp_zero F hF, mul_one]

/-- At every odd nonnegative integer, `theta` is `1` or `-1`; in
particular it is nonzero. -/
theorem paperTheta_odd_nat_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) (b : ℕ) :
    paperTheta F (2 * (b : ℝ) + 1) ≠ 0 := by
  rw [paperTheta_odd_nat_eq F hF b]
  exact pow_ne_zero _ (by norm_num)

/-- A centered level-`n` dyadic point.  The range
`0 ≤ a ≤ 2^(n+1)` parametrizes `[-1,1]`. -/
def centeredDyadic (n a : ℕ) : ℝ :=
  ((a : ℝ) - 2 ^ n) / 2 ^ n

/-- A centered dyadic whose numerator is in the defining range lies in the
closed support interval. -/
lemma centeredDyadic_mem_Icc (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) :
    centeredDyadic n a ∈ Icc (-1 : ℝ) 1 := by
  dsimp [centeredDyadic]
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  constructor
  · apply (le_div_iff₀ hp).2
    have ha0 : (0 : ℝ) ≤ a := by positivity
    linarith
  have haR : (a : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast ha
  rw [pow_succ] at haR
  apply (div_le_iff₀ hp).2
  nlinarith

private lemma centeredDyadic_scaled (n a k : ℕ) (hnk : n < k) :
    2 ^ k * (centeredDyadic n a + 1) =
      2 * ((2 ^ (k - n - 1) * a : ℕ) : ℝ) := by
  have hkn : k = n + (k - n) := by omega
  have hdiff : k - n = 1 + (k - n - 1) := by omega
  have hbase : centeredDyadic n a + 1 = (a : ℝ) / 2 ^ n := by
    dsimp [centeredDyadic]
    field_simp
    ring
  calc
    2 ^ k * (centeredDyadic n a + 1) =
        2 ^ (k - n) * (a : ℝ) := by
      rw [hbase, show (2 : ℝ) ^ k = 2 ^ (k - n) * 2 ^ n by
        rw [← pow_add, Nat.sub_add_cancel hnk.le]]
      field_simp
    _ = 2 * ((2 ^ (k - n - 1) * a : ℕ) : ℝ) := by
      nth_rw 1 [hdiff]
      rw [pow_add]
      push_cast
      ring

/-- At a level-`n` centered dyadic point, all derivatives of order strictly
larger than `n` vanish.  This is the precise truncation assertion preceding
equation (24). -/
theorem iteratedDeriv_rvachev_centeredDyadic_eq_zero
    (F : BoundedFabius) (hF : IsFabius F)
    (n a k : ℕ) (ha : a ≤ 2 ^ (n + 1)) (hnk : n < k) :
    iteratedDeriv k (rvachevUp F) (centeredDyadic n a) = 0 := by
  rw [original_theorem_four_c F hF k (centeredDyadic n a)
    (centeredDyadic_mem_Icc n a ha)]
  have harg : 2 ^ k * centeredDyadic n a + 2 ^ k =
      2 ^ k * (centeredDyadic n a + 1) := by ring
  rw [harg, centeredDyadic_scaled n a k hnk,
    paperTheta_even_nat_eq_zero F hF, mul_zero]

/-- If the dyadic numerator is odd, the derivative of order `n` is nonzero,
so the Taylor polynomial in equation (24) has degree exactly `n`. -/
theorem iteratedDeriv_rvachev_centeredDyadic_ne_zero
    (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) (haOdd : Odd a) :
    iteratedDeriv n (rvachevUp F) (centeredDyadic n a) ≠ 0 := by
  obtain ⟨b, rfl⟩ := haOdd
  rw [original_theorem_four_c F hF n (centeredDyadic n (2 * b + 1))
    (centeredDyadic_mem_Icc n (2 * b + 1) ha)]
  have harg :
      2 ^ n * centeredDyadic n (2 * b + 1) + 2 ^ n =
        2 * (b : ℝ) + 1 := by
    dsimp [centeredDyadic]
    field_simp
    push_cast
    ring
  rw [harg]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (paperTheta_odd_nat_ne_zero F hF b)

/-- An in-range centered dyadic with odd numerator lies in the interior of
the support interval. -/
lemma centeredDyadic_mem_Ioo_of_odd
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) (haOdd : Odd a) :
    centeredDyadic n a ∈ Ioo (-1 : ℝ) 1 := by
  have ha0 : 0 < a := haOdd.pos
  have halt : a < 2 ^ (n + 1) := by
    obtain ⟨b, rfl⟩ := haOdd
    rw [pow_succ] at ha ⊢
    omega
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  dsimp [centeredDyadic]
  constructor
  · apply (lt_div_iff₀ hp).2
    have ha0R : (0 : ℝ) < a := by exact_mod_cast ha0
    linarith
  · apply (div_lt_iff₀ hp).2
    have haltR : (a : ℝ) < (2 : ℝ) ^ (n + 1) := by exact_mod_cast halt
    rw [pow_succ] at haltR
    linarith

/-- The finite Taylor polynomial displayed in equation (24). -/
noncomputable def rvachevDyadicTaylorPolynomial
    (F : BoundedFabius) (n a : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (n + 1),
    Polynomial.C (iteratedDeriv k (rvachevUp F) (centeredDyadic n a) /
      (k.factorial : ℝ)) * Polynomial.X ^ k

/-- Evaluation of the polynomial in equation (24). -/
theorem rvachevDyadicTaylorPolynomial_eval
    (F : BoundedFabius) (n a : ℕ) (x : ℝ) :
    (rvachevDyadicTaylorPolynomial F n a).eval x =
      ∑ k ∈ range (n + 1),
        iteratedDeriv k (rvachevUp F) (centeredDyadic n a) /
          (k.factorial : ℝ) * x ^ k := by
  rw [rvachevDyadicTaylorPolynomial, Polynomial.eval_finsetSum]
  simp

/-- The Taylor polynomial at a level-`n` dyadic has degree at most `n`. -/
theorem rvachevDyadicTaylorPolynomial_natDegree_le
    (F : BoundedFabius) (n a : ℕ) :
    (rvachevDyadicTaylorPolynomial F n a).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  simp [rvachevDyadicTaylorPolynomial, Nat.not_le.mpr hN]

/-- For an odd numerator the Taylor polynomial has degree exactly `n`. -/
theorem rvachevDyadicTaylorPolynomial_natDegree_eq
    (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) (haOdd : Odd a) :
    (rvachevDyadicTaylorPolynomial F n a).natDegree = n := by
  apply le_antisymm (rvachevDyadicTaylorPolynomial_natDegree_le F n a)
  apply Polynomial.le_natDegree_of_ne_zero
  simp only [rvachevDyadicTaylorPolynomial]
  simp
  exact ⟨iteratedDeriv_rvachev_centeredDyadic_ne_zero F hF n a ha haOdd,
    n.factorial_ne_zero⟩

/-! ## The nowhere-analytic corollary -/

/-- Dyadic meshes become arbitrarily fine while their level stays above any
prescribed cutoff. -/
private lemma exists_level_ge_one_div_two_pow_lt
    (r : ℝ) (hr : 0 < r) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 / (2 : ℝ) ^ n < r := by
  obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one hr
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N + d, by omega, ?_⟩
  rw [show 1 / (2 : ℝ) ^ (N + d) = (1 / 2 : ℝ) ^ (N + d) by
    rw [div_pow]
    norm_num]
  rw [pow_add]
  calc
    (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ d ≤
        1 * (1 / 2 : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num))
        (by positivity)
    _ < r := by simpa using hd

/-- Odd centered dyadics of arbitrarily high level occur in every ball whose
center is in the interior of `[-1,1]`. -/
private theorem exists_odd_centeredDyadic_mem_ball_of_mem_Ioo
    (x r : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) (hr : 0 < r) (N : ℕ) :
    ∃ n a : ℕ, N ≤ n ∧ a ≤ 2 ^ (n + 1) ∧ Odd a ∧
      centeredDyadic n a ∈ Metric.ball x r := by
  obtain ⟨n, hnN1, hmesh⟩ :=
    exists_level_ge_one_div_two_pow_lt r hr (N + 1)
  have hnN : N ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  let scale : ℝ := 2 ^ (n - 1)
  have hscale : 0 < scale := by positivity
  have hpow : (2 : ℝ) ^ n = 2 * scale := by
    dsimp [scale]
    nth_rw 1 [show n = n - 1 + 1 by omega]
    rw [pow_succ]
    ring
  let u : ℝ := scale * (x + 1)
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact mul_nonneg hscale.le (by linarith [hx.1])
  let b : ℕ := ⌊u⌋₊
  have hb_le : (b : ℝ) ≤ u := by
    exact Nat.floor_le hu0
  have hu_lt : u < (b : ℝ) + 1 := by
    exact Nat.lt_floor_add_one u
  have hu_pow : u < (2 : ℝ) ^ n := by
    dsimp [u]
    rw [hpow]
    nlinarith [hx.2, hscale]
  have hb_lt_real : (b : ℝ) < (2 : ℝ) ^ n := hb_le.trans_lt hu_pow
  have hb_lt : b < 2 ^ n := by exact_mod_cast hb_lt_real
  let a := 2 * b + 1
  have ha : a ≤ 2 ^ (n + 1) := by
    dsimp [a]
    rw [pow_succ]
    omega
  have haOdd : Odd a := ⟨b, by simp [a, two_mul]⟩
  have hy_sub : centeredDyadic n a - x =
      ((b : ℝ) + 1 / 2 - u) / scale := by
    dsimp [centeredDyadic, a, u]
    push_cast
    rw [hpow]
    field_simp
    ring
  have hnum : |(b : ℝ) + 1 / 2 - u| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hdist : dist (centeredDyadic n a) x < r := by
    rw [Real.dist_eq, hy_sub, abs_div, abs_of_pos hscale]
    calc
      |(b : ℝ) + 1 / 2 - u| / scale ≤ (1 / 2) / scale :=
        div_le_div_of_nonneg_right hnum hscale.le
      _ = 1 / (2 : ℝ) ^ n := by rw [hpow]; field_simp
      _ < r := hmesh
  exact ⟨n, a, hnN, ha, haOdd, Metric.mem_ball.2 hdist⟩

/-- Odd centered dyadics of arbitrarily high level occur in every ball
centered at a point of `[-1,1]`. -/
private theorem exists_odd_centeredDyadic_mem_ball
    (x r : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (hr : 0 < r) (N : ℕ) :
    ∃ n a : ℕ, N ≤ n ∧ a ≤ 2 ^ (n + 1) ∧ Odd a ∧
      centeredDyadic n a ∈ Metric.ball x r := by
  rcases eq_or_lt_of_le hx.1 with hleft | hleft
  · have hxeq : x = -1 := hleft.symm
    subst x
    obtain ⟨n, hnN, hmesh⟩ := exists_level_ge_one_div_two_pow_lt r hr N
    refine ⟨n, 1, hnN, Nat.one_le_two_pow, ⟨0, by simp⟩, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have hy : centeredDyadic n 1 - (-1 : ℝ) = 1 / 2 ^ n := by
      dsimp [centeredDyadic]
      field_simp
      norm_num
    rw [hy, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ n)]
    exact hmesh
  · rcases eq_or_lt_of_le hx.2 with hright | hright
    · have hxeq : x = 1 := hright
      subst x
      obtain ⟨n, hnN, hmesh⟩ := exists_level_ge_one_div_two_pow_lt r hr N
      let a := 2 ^ (n + 1) - 1
      have ha : a ≤ 2 ^ (n + 1) := Nat.sub_le _ _
      have haOdd : Odd a := by
        dsimp [a]
        rw [show n + 1 = 1 + n by omega, pow_add]
        refine ⟨2 ^ n - 1, ?_⟩
        have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      refine ⟨n, a, hnN, ha, haOdd, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have hp : (0 : ℝ) < 2 ^ n := by positivity
      have haCast : (a : ℝ) = (2 : ℝ) ^ (n + 1) - 1 := by
        dsimp [a]
        rw [Nat.cast_sub (Nat.one_le_two_pow : 1 ≤ 2 ^ (n + 1))]
        push_cast
        rfl
      rw [centeredDyadic, haCast, pow_succ]
      have : ((2 * 2 ^ n - 1 - 2 ^ n) / 2 ^ n - 1 : ℝ) =
          -(1 / 2 ^ n) := by field_simp; ring
      rw [show (2 : ℝ) ^ n * 2 = 2 * 2 ^ n by ring, this, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ n)]
      exact hmesh
    · exact exists_odd_centeredDyadic_mem_ball_of_mem_Ioo x r ⟨hleft, hright⟩ hr N

/-- The unnumbered corollary following equation (24): Rvachev's compactly
supported function is not real analytic at any point of its support. -/
theorem rvachev_not_analyticAt
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    ¬ AnalyticAt ℝ (rvachevUp F) x := by
  intro hxAnalytic
  obtain ⟨r, hr, hAnalyticOn⟩ := hxAnalytic.exists_ball_analyticOnNhd
  obtain ⟨n, a, _hn, ha, haOdd, hyBall⟩ :=
    exists_odd_centeredDyadic_mem_ball x r hx hr 0
  let y := centeredDyadic n a
  have hyAnalytic : AnalyticAt ℝ (rvachevUp F) y :=
    hAnalyticOn y hyBall
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ
      (fun k ↦ iteratedDeriv k (rvachevUp F) y / (k.factorial : ℝ))
  obtain ⟨ρ, hp⟩ := hyAnalytic.hasFPowerSeriesAt
  have hpFinite : HasFiniteFPowerSeriesOnBall (rvachevUp F) p y (n + 1) ρ := {
    toHasFPowerSeriesOnBall := by simpa only [p] using hp
    finite := by
      intro k hk
      have hkgt : n < k := by omega
      have hzero := iteratedDeriv_rvachev_centeredDyadic_eq_zero
        F hF n a k ha hkgt
      simp [p, y, hzero]
  }
  obtain ⟨δ, hδ0, hδρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hδpos : 0 < (δ : ℝ) := by
    exact_mod_cast (ENNReal.coe_pos.mp hδ0)
  have hyIoo : y ∈ Ioo (-1 : ℝ) 1 :=
    centeredDyadic_mem_Ioo_of_odd n a ha haOdd
  obtain ⟨m, c, hnm, hc, hcOdd, hzBall⟩ :=
    exists_odd_centeredDyadic_mem_ball_of_mem_Ioo y (δ : ℝ) hyIoo hδpos (n + 1)
  let z := centeredDyadic m c
  have hnorm : (↑‖z - y‖₊ : ENNReal) < ρ := by
    have hnear : edist z y < (δ : ENNReal) := by
      rw [edist_lt_coe]
      apply (NNReal.coe_lt_coe.mp)
      change dist z y < (δ : ℝ)
      exact Metric.mem_ball.mp hzBall
    change (↑(nndist z y) : ENNReal) < ρ
    exact hnear.trans hδρ
  have hpAtZ := hpFinite.changeOrigin (y := z - y) hnorm
  have hyz : y + (z - y) = z := by ring
  rw [hyz] at hpAtZ
  have hDerivZero : iteratedDeriv m (rvachevUp F) z = 0 := by
    rw [iteratedDeriv_eq_iteratedFDeriv,
      hpAtZ.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace
        (fun _ : Fin m ↦ (1 : ℝ)),
      hpAtZ.finite m hnm]
    simp
  exact (iteratedDeriv_rvachev_centeredDyadic_ne_zero F hF m c hc hcOdd)
    hDerivZero

/-! ## Theorems 6 and 7 -/

/-- Theorem 6, equations (33)--(34), with the necessary hypothesis `1 ≤ n`
on the first formula made explicit. -/
theorem original_theorem_six
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    ((∫ t in (0 : ℝ)..1, t ^ (n - 1) * rvachevUp F t) =
        (Nat.factorial (n - 1) : ℝ) * 2 ^ n.choose 2 *
          rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹)) ∧
      (∀ m : ℕ, (∫ t in (0 : ℝ)..1, t ^ (2 * m) * rvachevUp F t) =
        (moment m : ℝ) / 2) := by
  constructor
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h := halfIntegral_eq_rvachev_dyadic_formula F hF (1 + m) (by omega)
    have hnR : ((1 + m : ℕ) : ℝ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hnR)
    simpa [Nat.factorial_succ, add_comm, mul_assoc, mul_left_comm, mul_comm] using h
  · intro m
    exact (moment_halfIntegral_eq_rvachev_dyadic_formula F hF m).1.symm

/-- Theorem 7: every value on the dyadic grid is rational, with an explicit
rational witness computed by `fabiusDyadic`. -/
theorem original_theorem_seven
    (F : BoundedFabius) (hF : IsFabius F) (n a : ℕ)
    (ha : a ≤ 2 ^ (n + 1)) :
    ∃ q : ℚ, (q : ℝ) = rvachevUp F (centeredDyadic n a) := by
  refine ⟨fabiusDyadic n a, (fabiusDyadic_cast_extended_formula F hF n a ha).trans ?_⟩
  rw [extendedFabius_eq_single_translate F hF 0 (by
    norm_num
    positivity) ?_]
  · simp [binaryWeight, centeredDyadic]
    congr 1
    field_simp
  · have haR : (a : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast ha
    rw [pow_succ] at haR
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).2
    simpa [mul_comm] using haR

/-- The signed dyadic evaluator agrees with Rvachev's function for every
integer numerator.  Outside `[-1,1]` both sides vanish, so this removes the
support restriction from `rvachevDyadic_cast`. -/
theorem rvachevDyadic_cast_global
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (a : ℤ) :
    (rvachevDyadic n a : ℝ) = rvachevUp F (a / (2 : ℝ) ^ n) := by
  by_cases ha : a.natAbs ≤ 2 ^ n
  · exact rvachevDyadic_cast F hF n a ha
  · have halt : 2 ^ n < a.natAbs := Nat.lt_of_not_ge ha
    have habs : 1 < |(a : ℝ) / (2 : ℝ) ^ n| := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      rw [one_lt_div (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      have hcast : (2 : ℝ) ^ n < (a.natAbs : ℝ) := by
        exact_mod_cast halt
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    have hzero : rvachevUp F ((a : ℝ) / (2 : ℝ) ^ n) = 0 := by
      apply rvachevUp_eq_zero_of_not_mem_Ioo F hF
      intro hx
      have hxabs : |(a : ℝ) / (2 : ℝ) ^ n| < 1 := (abs_lt).2 hx
      linarith
    rw [rvachevDyadic, if_neg ha, Rat.cast_zero, hzero]

/-- Theorem 7 in its literal global form: Rvachev's function is rational at
every dyadic point, including the points outside its compact support. -/
theorem original_theorem_seven_global
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (a : ℤ) :
    ∃ q : ℚ, (q : ℝ) = rvachevUp F (a / (2 : ℝ) ^ n) :=
  ⟨rvachevDyadic n a, rvachevDyadic_cast_global F hF n a⟩

end

end Fabius
