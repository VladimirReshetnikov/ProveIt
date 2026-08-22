import FabiusFunction.Basic
import FabiusFunction.DyadicCorrectness
import FabiusFunction.MomentPowerSeries
import FabiusFunction.NormalizedMoments
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Statements from *Arithmetic of the Fabius function*

This module formalizes every proved result in Juan Arias de Reyna,
*Arithmetic of the Fabius function*, arXiv:1702.06487v3.  It also records the
paper's Question 5, Definition 12, and Conjecture 16.  Proofs are intentionally
left as `sorry` in this first statement-only phase.

There are two deliberate corrections/clarifications:

* `fabius : ℝ → Set.Icc 0 1` is the bounded CDF requested for this project,
  while `extendedFabius : ℝ → ℝ` is the signed global function used by the
  paper outside `[0,1]`.
* Lemma 1 in the paper is false as printed.  Its proof requires the additional
  hypothesis `0 ≤ scale + order`; that hypothesis is included below.

Exact values, denominators, divisibility, and valuations live in `ℚ` or `ℕ`.
The bridge theorems below are the boundary between that arithmetic layer and
the analytic functions.
-/

set_option autoImplicit false

open scoped BigOperators Interval
open Finset MeasureTheory Set

namespace Fabius

noncomputable section

/-! ## The distinguished Fabius function -/

/-- Existence and uniqueness for the bounded/CDF characterization. -/
theorem existsUnique_fabius :
    ∃! F : BoundedFabius, IsFabius F := by
  sorry

/-- The canonical bounded Fabius function `ℝ → [0,1]`. -/
noncomputable def fabius : BoundedFabius :=
  Classical.choose existsUnique_fabius

/-- The canonical function satisfies the defining Fabius properties. -/
theorem fabius_spec : IsFabius fabius :=
  (Classical.choose_spec existsUnique_fabius).1

/-- The assumed convention: the canonical bounded function is zero on `(-∞,0]`. -/
theorem fabius_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    fabiusReal fabius x = 0 :=
  fabius_spec.zero_of_nonpos x hx

/-- The clamped bounded function is one to the right of the unit interval. -/
theorem fabius_eq_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    fabiusReal fabius x = 1 :=
  fabius_spec.one_of_one_le x hx

/-- The signed global extension of the canonical bounded function. -/
noncomputable def globalFabius : ℝ → ℝ :=
  extendedFabius fabius

/-! ## Analytic and exact-arithmetic bridges -/

/-- The differential equation makes the Fabius function monotone on its first half. -/
theorem fabius_monotoneOn_firstHalf (F : BoundedFabius) (hF : IsFabius F) :
    MonotoneOn (fabiusReal F) (Icc (0 : ℝ) (1 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (1 / 2))
      hF.contDiff.continuous.continuousOn
      (hF.contDiff.differentiable (by simp)).differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(hF.hasDerivAt x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).deriv]
  exact mul_nonneg (by norm_num) (fabiusReal_nonneg F (2 * x))

/-- Symmetry transfers first-half monotonicity to the second half. -/
theorem fabius_monotoneOn_secondHalf (F : BoundedFabius) (hF : IsFabius F) :
    MonotoneOn (fabiusReal F) (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  have hreflectx : 1 - x ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hreflecty : 1 - y ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith [hy.1, hy.2]
  have hmono := fabius_monotoneOn_firstHalf F hF hreflecty hreflectx (by linarith)
  rw [hF.symmetry x ⟨by linarith [hx.1], hx.2⟩,
    hF.symmetry y ⟨by linarith [hy.1], hy.2⟩] at hmono
  linarith

/-- The bounded/CDF Fabius function is monotone on all of `ℝ`. -/
theorem fabius_monotone (F : BoundedFabius) (hF : IsFabius F) :
    Monotone (fabiusReal F) := by
  intro x y hxy
  by_cases hy0 : y ≤ 0
  · rw [hF.zero_of_nonpos y hy0, hF.zero_of_nonpos x (hxy.trans hy0)]
  by_cases hx0 : x ≤ 0
  · rw [hF.zero_of_nonpos x hx0]
    exact fabiusReal_nonneg F y
  have hxpos : 0 < x := lt_of_not_ge hx0
  by_cases hx1 : 1 ≤ x
  · rw [hF.one_of_one_le x hx1, hF.one_of_one_le y (hx1.trans hxy)]
  by_cases hy1 : 1 ≤ y
  · rw [hF.one_of_one_le y hy1]
    exact fabiusReal_le_one F x
  have hxmem : x ∈ Icc (0 : ℝ) 1 := ⟨hxpos.le, le_of_not_ge hx1⟩
  have hymem : y ∈ Icc (0 : ℝ) 1 :=
    ⟨le_of_not_ge hy0, le_of_not_ge hy1⟩
  by_cases hyhalf : y ≤ 1 / 2
  · exact fabius_monotoneOn_firstHalf F hF
      ⟨hxmem.1, hxy.trans hyhalf⟩ ⟨hymem.1, hyhalf⟩ hxy
  by_cases hxhalf : 1 / 2 ≤ x
  · exact fabius_monotoneOn_secondHalf F hF
      ⟨hxhalf, hxmem.2⟩ ⟨le_of_not_ge hyhalf, hymem.2⟩ hxy
  · exact (fabius_monotoneOn_firstHalf F hF
        ⟨hxmem.1, le_of_not_ge hxhalf⟩ ⟨by norm_num, by norm_num⟩
          (le_of_not_ge hxhalf)).trans
      (fabius_monotoneOn_secondHalf F hF
        ⟨by norm_num, by norm_num⟩ ⟨le_of_not_ge hyhalf, hymem.2⟩
          (le_of_not_ge hyhalf))

/-- A zero on the first half would force a zero at twice the argument. -/
theorem fabius_zero_double (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hz : fabiusReal F x = 0) : fabiusReal F (2 * x) = 0 := by
  have hmin : IsMinOn (fabiusReal F) Set.univ x := by
    intro y hy
    rw [hz]
    exact fabiusReal_nonneg F y
  have hderiv : deriv (fabiusReal F) x = 0 :=
    (hmin.isLocalMin Filter.univ_mem).deriv_eq_zero
  rw [(hF.hasDerivAt x ⟨hx0, hxhalf⟩).deriv] at hderiv
  linarith

private theorem index_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

/-- The Fabius function is strictly positive at every positive argument. -/
theorem fabius_pos_of_pos (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : 0 < x) : 0 < fabiusReal F x := by
  by_contra hnot
  have hz : fabiusReal F x = 0 :=
    le_antisymm (le_of_not_gt hnot) (fabiusReal_nonneg F x)
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / 2 : ℝ) / x)
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast index_le_two_pow N
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ≤ (2 : ℝ) ^ n * x := by
    refine ⟨N, ?_⟩
    have : (1 / 2 : ℝ) < (N : ℝ) * x := by
      rw [div_lt_iff₀ hx] at hN
      linarith
    nlinarith
  let n := Nat.find hex
  have hnreach : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ n * x := Nat.find_spec hex
  have hzero_iter : ∀ m : ℕ, m ≤ n →
      fabiusReal F ((2 : ℝ) ^ m * x) = 0 := by
    intro m hm
    induction m with
    | zero => simpa using hz
    | succ m ih =>
        have hm_lt : m < n := by omega
        have hnotreach : ¬ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ m * x := by
          intro hreach
          exact (Nat.not_lt_of_ge (Nat.find_min' hex hreach)) hm_lt
        have hxm_nonneg : 0 ≤ (2 : ℝ) ^ m * x := by positivity
        have hxm_half : (2 : ℝ) ^ m * x ≤ 1 / 2 := le_of_not_ge hnotreach
        have hdoubled := fabius_zero_double F hF hxm_nonneg hxm_half (ih (by omega))
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hdoubled
  have hhalf_le_zero := fabius_monotone F hF
      (show (1 / 2 : ℝ) ≤ (2 : ℝ) ^ n * x from hnreach)
  rw [hzero_iter n le_rfl] at hhalf_le_zero
  have hhalf : fabiusReal F (1 / 2) = 1 / 2 := by
    have hs := hF.symmetry (1 / 2) (by constructor <;> norm_num)
    norm_num at hs ⊢
    linarith
  rw [hhalf] at hhalf_le_zero
  norm_num at hhalf_le_zero

/-- Values strictly left of one are strictly below one. -/
theorem fabius_lt_one_of_lt_one (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x < 1) : fabiusReal F x < 1 := by
  by_cases hx0 : x ≤ 0
  · rw [hF.zero_of_nonpos x hx0]
    norm_num
  · have hmem : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_ge hx0, hx.le⟩
    have hpos : 0 < fabiusReal F (1 - x) :=
      fabius_pos_of_pos F hF (by linarith)
    rw [hF.symmetry x hmem] at hpos
    linarith

/-- Rvachev's function is smooth. -/
theorem rvachev_contDiff (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℝ ⊤ (rvachevUp F) := by
  sorry

/-- Rvachev's function is even. -/
theorem rvachev_even (F : BoundedFabius) (hF : IsFabius F) :
    Function.Even (rvachevUp F) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hxpos : 0 < x
  · have hnx : -x ≤ 0 := by linarith
    have hxnot : ¬ x ≤ 0 := not_le.mpr hxpos
    simp only [rvachevUp, if_pos hnx, if_neg hxnot]
    congr 1
    ring
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    have hnxnot : ¬ -x ≤ 0 := by linarith
    have hxle : x ≤ 0 := hxneg.le
    simp only [rvachevUp, if_neg hnxnot, if_pos hxle]
    congr 1
    ring

/-- Rvachev's function is supported in `[-1,1]`. -/
theorem support_rvachev_subset (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (rvachevUp F) ⊆ Icc (-1 : ℝ) 1 := by
  intro x hx
  constructor
  · by_contra h
    have hxlt : x < -1 := lt_of_not_ge h
    have hxle : x ≤ 0 := by linarith
    have hxarg : x + 1 ≤ 0 := by linarith
    apply hx
    rw [rvachevUp, if_pos hxle]
    exact hF.zero_of_nonpos _ hxarg
  · by_contra h
    have hxgt : 1 < x := lt_of_not_ge h
    have hxnot : ¬ x ≤ 0 := by linarith
    have hxarg : 1 - x ≤ 0 := by linarith
    apply hx
    rw [rvachevUp, if_neg hxnot]
    exact hF.zero_of_nonpos _ hxarg

/-- The topological support is exactly the compact interval `[-1,1]`. -/
theorem tsupport_rvachev (F : BoundedFabius) (hF : IsFabius F) :
    tsupport (rvachevUp F) = Icc (-1 : ℝ) 1 := by
  have hinterior : Ioo (-1 : ℝ) 1 ⊆ Function.support (rvachevUp F) := by
    intro x hx
    change rvachevUp F x ≠ 0
    by_cases hx0 : x ≤ 0
    · unfold rvachevUp
      rw [if_pos hx0]
      exact ne_of_gt (fabius_pos_of_pos F hF (by linarith [hx.1]))
    · unfold rvachevUp
      rw [if_neg hx0]
      exact ne_of_gt (fabius_pos_of_pos F hF (by linarith [hx.2]))
  apply Set.Subset.antisymm
  · exact closure_minimal (support_rvachev_subset F hF) isClosed_Icc
  · rw [← closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact closure_mono hinterior

/-- Normalization of Rvachev's function. -/
theorem rvachev_zero (F : BoundedFabius) (hF : IsFabius F) : rvachevUp F 0 = 1 := by
  rw [rvachevUp, if_pos le_rfl]
  simpa [fabiusReal] using hF.one_of_one_le 1 le_rfl

/-- The differential equation defining Rvachev's function. -/
theorem rvachev_hasDerivAt (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (rvachevUp F)
      (2 * (rvachevUp F (2 * x + 1) - rvachevUp F (2 * x - 1))) x := by
  sorry

/-- The signed global extension is smooth. -/
theorem extendedFabius_contDiff (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℝ ⊤ (extendedFabius F) := by
  sorry

/-- The signed extension vanishes on nonpositive arguments. -/
theorem extendedFabius_eq_zero_of_nonpos (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ≤ 0) : extendedFabius F x = 0 := by
  unfold extendedFabius
  rw [tsum_eq_single 0]
  · norm_num [binaryWeight, rvachevUp]
    rw [if_pos (hx.trans (by norm_num))]
    exact hF.zero_of_nonpos _ hx
  · intro n hn
    have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnposReal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have harg : x - 2 * (n : ℝ) - 1 ≤ 0 := by linarith
    have hinside : x - 2 * (n : ℝ) - 1 + 1 ≤ 0 := by linarith
    rw [rvachevUp, if_pos harg, hF.zero_of_nonpos _ hinside]
    simp

/-- The bounded and signed versions agree on the unit interval. -/
theorem extendedFabius_eq_fabiusReal (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extendedFabius F x = fabiusReal F x := by
  unfold extendedFabius
  rw [tsum_eq_single 0]
  · norm_num [binaryWeight, rvachevUp, hx.2]
  · intro n hn
    have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnposReal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have harg : x - 2 * (n : ℝ) - 1 ≤ 0 := by
      linarith [hx.2]
    have hinside : x - 2 * (n : ℝ) - 1 + 1 ≤ 0 := by
      linarith [hx.2]
    rw [rvachevUp, if_pos harg, hF.zero_of_nonpos _ hinside]
    simp

/-- The global Fabius differential equation. -/
theorem extendedFabius_hasDerivAt (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (extendedFabius F) (2 * extendedFabius F (2 * x)) x := by
  sorry

/-- Equation (3): every iterated derivative is a rescaled Fabius value. -/
theorem iteratedDeriv_extendedFabius (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (x : ℝ) :
    iteratedDeriv k (extendedFabius F) x =
      2 ^ (k + 1).choose 2 * extendedFabius F (2 ^ k * x) := by
  sorry

/-- The corresponding iterated-derivative formula for Rvachev's function. -/
theorem iteratedDeriv_rvachev (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDeriv n (rvachevUp F) x =
      2 ^ (n + 1).choose 2 * extendedFabius F (2 ^ n * (x + 1)) := by
  sorry

/-- Equations (5) and (7): the Fourier transform, sinc product, and moment series agree. -/
theorem rvachevFourier_eq_product_eq_series
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevFourier F z = rvachevFourierProduct z ∧
      rvachevFourierProduct z = rvachevMomentSeries z := by
  sorry

/-- Equation (6): Fourier inversion for Rvachev's function. -/
theorem rvachev_fourier_inversion
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    (rvachevUp F x : ℂ) =
      ∫ t : ℝ, rvachevFourier F t *
        Complex.exp (2 * Real.pi * Complex.I * t * x) := by
  sorry

/-- The Fourier transform of Rvachev's function is entire. -/
theorem rvachevFourier_differentiable (F : BoundedFabius) (hF : IsFabius F) :
    Differentiable ℂ (rvachevFourier F) := by
  sorry

/-- Equation (17): the analytic generating function has coefficients `d_n`. -/
theorem complexGeneratingFunction_eq_series
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z = halfMomentGeneratingSeries z := by
  sorry

/-- The second equality in equation (20), expressed using the Fourier transform. -/
theorem complexGeneratingFunction_eq_fourier
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z =
      Complex.exp (z / 2) *
        rvachevFourier F (Complex.I * z / (4 * Real.pi)) := by
  sorry

/-- Equation (8): `moment n` is the `2n`-th moment of `rvachev`. -/
theorem moment_eq_integral (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (moment n : ℝ) = momentIntegral F n := by
  sorry

/-- Equation (21), whose integral form starts at `n = 1`. -/
theorem halfMoment_eq_integral (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    (halfMoment n : ℝ) = halfMomentIntegral F n := by
  sorry

/-- Equations (21)--(22), connecting `d_n` to the bounded Fabius function. -/
theorem halfMoment_eq_fabius (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (halfMoment n : ℝ) =
      n.factorial * 2 ^ n.choose 2 * fabiusReal F (((2 : ℝ) ^ n)⁻¹) := by
  sorry

/-- Equation (14), directly relating a half integral to a dyadic `up` value. -/
theorem halfIntegral_eq_rvachev_dyadic
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * ∫ t in (0 : ℝ)..1, t ^ (n - 1) * rvachevUp F t =
      n.factorial * 2 ^ n.choose 2 *
        rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹) := by
  sorry

/-- Equation (15), specializing equation (14) to an even moment. -/
theorem moment_halfIntegral_eq_rvachev_dyadic
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (moment n : ℝ) / 2 =
        ∫ t in (0 : ℝ)..1, t ^ (2 * n) * rvachevUp F t ∧
    (∫ t in (0 : ℝ)..1, t ^ (2 * n) * rvachevUp F t) =
      (Nat.factorial (2 * n) : ℝ) * 2 ^ (2 * n + 1).choose 2 *
        rvachevUp F (1 - ((2 : ℝ) ^ (2 * n + 1))⁻¹) := by
  sorry

/-- Equation (16), the odd inverse-power value in terms of `F_n`. -/
theorem fabiusAtInverseTwoPow_odd (n : ℕ) :
    fabiusAtInverseTwoPow (2 * n + 1) =
      (momentNumerator n : ℚ) /
        ((2 : ℚ) ^ (2 * n + 1).choose 2 * 2 * Nat.factorial (2 * n) *
          oddDoubleFactorial (n + 1) * evenMersenneProduct n) := by
  sorry

/-- Equation (25), the general inverse-power value in terms of `G_n`. -/
theorem fabiusAtInverseTwoPow_eq_halfMomentNumerator (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (halfMomentNumerator n : ℚ) /
        ((2 : ℚ) ^ n.choose 2 * n.factorial * (n + 1).factorial *
          mersenneProduct n) := by
  sorry

/-- Equation (26) and its natural divisibility consequence. -/
theorem halfMomentNumerator_odd_index (n : ℕ) :
    (halfMomentNumerator (2 * n + 1) : ℚ) / (2 * n + 1) =
      ((2 ^ n * (n + 1).factorial * momentNumerator n *
        oddMersenneProduct n : ℕ) : ℚ) ∧
    (2 * n + 1) * momentNumerator n ∣ halfMomentNumerator (2 * n + 1) := by
  sorry

/-! ## Correctness specifications for the executable dyadic evaluator -/

/-- The precomputed table contains the exact values `F(2⁻ᵏ)`. -/
theorem fabiusInversePowTwoTable_get (maxExponent k : ℕ) (hk : k ≤ maxExponent) :
    (fabiusInversePowTwoTable maxExponent)[k]? = some (fabiusAtInverseTwoPow k) := by
  induction maxExponent generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp [fabiusInversePowTwoTable,
        fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue]
  | succ n ih =>
      rw [fabiusInversePowTwoTable, Array.getElem?_push,
        fabiusInversePowTwoTable_size]
      by_cases hlast : k = n + 1
      · subst k
        simp only [ite_true]
        congr 1
        rw [fabiusAtInverseTwoPow_eq_halfMoment,
          halfMomentFabiusValue_succ]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j.val (by omega)]
        simp [fabiusAtInverseTwoPow_eq_halfMoment]
      · rw [if_neg hlast]
        exact ih k (by omega)

/-- The Horner routine evaluates the Taylor polynomial in Proposition 10. -/
theorem fabiusTaylorHorner_eq_sum (maxExponent order : ℕ)
    (horder : order ≤ maxExponent) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable maxExponent) order offset =
      ∑ k ∈ range (order + 1),
        (2 : ℚ) ^ (k + 1).choose 2 * fabiusAtInverseTwoPow (order - k) *
          offset ^ k / k.factorial := by
  have hzero : fabiusInversePowTwoTableValue
      (fabiusInversePowTwoTable maxExponent) 0 = 1 := by
    rw [fabiusInversePowTwoTableValue,
      fabiusInversePowTwoTable_get maxExponent 0 (Nat.zero_le _)]
    simp [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue]
  change fabiusTaylorHorner.go (fabiusInversePowTwoTable maxExponent)
      order offset order = _
  have hgo := fabiusTaylorHorner_go_eq_sum
    (fabiusInversePowTwoTable maxExponent) hzero offset order 0
  simp only [Nat.zero_add] at hgo
  rw [hgo]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ order := by simpa using hk
  have hlookup := fabiusInversePowTwoTable_get maxExponent (order - k)
    (le_trans (Nat.sub_le order k) horder)
  rw [fabiusInversePowTwoTableValue, hlookup]
  norm_num

/-- On the unit dyadic grid, the fast recursion agrees with equation (32). -/
theorem fabiusDyadicUnit_eq_fabiusDyadic (n a : ℕ) (ha : a ≤ 2 ^ n) :
    fabiusDyadicUnit n a = fabiusDyadic n a := by
  sorry

/-- Equation (32) really evaluates the bounded Fabius function on its dyadic grid. -/
theorem fabiusDyadic_cast (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ n) :
    (fabiusDyadic n a : ℝ) = fabiusReal F (a / (2 : ℝ) ^ n) := by
  sorry

/-- Equation (32) on its full `[0,2]` range, using the signed extension. -/
theorem fabiusDyadic_cast_extended (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) :
    (fabiusDyadic n a : ℝ) =
      extendedFabius F (a / (2 : ℝ) ^ n) := by
  sorry

/-- The total signed-numerator evaluator computes the bounded Fabius function. -/
theorem fabiusDyadicValue_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (a : ℤ) :
    (fabiusDyadicValue n a : ℝ) =
      fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) := by
  by_cases ha : a ≤ 0
  · rw [fabiusDyadicValue_of_nonpos n a ha]
    norm_num
    apply (hF.zero_of_nonpos _ ?_).symm
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast ha) (by positivity)
  · have hapos : 0 < a := lt_of_not_ge ha
    by_cases hge : (2 ^ n : ℤ) ≤ a
    · rw [fabiusDyadicValue_of_ge n a hge]
      norm_num
      apply (hF.one_of_one_le _ ?_).symm
      rw [le_div_iff₀' (by positivity : (0 : ℝ) < 2 ^ n)]
      norm_num at hge ⊢
      exact_mod_cast hge
    · rw [fabiusDyadicValue, if_neg ha]
      have htoNat : (a.toNat : ℤ) = a := Int.toNat_of_nonneg hapos.le
      have hbound : a.toNat ≤ 2 ^ n := by
        exact ((Int.toNat_lt hapos.le).2 (lt_of_not_ge hge)).le
      rw [fabiusDyadicUnit_eq_fabiusDyadic n a.toNat hbound,
        fabiusDyadic_cast F hF n a.toNat hbound]
      congr 1
      rw [show (a.toNat : ℝ) = (a : ℝ) by exact_mod_cast htoNat]

/-- The analogous exact evaluator computes the paper's signed global extension. -/
theorem extendedFabiusDyadicValue_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (a : ℤ) :
    (extendedFabiusDyadicValue n a : ℝ) =
      extendedFabius F ((a : ℝ) / (2 : ℝ) ^ n) := by
  sorry

/-- A successful rational-input evaluation has the correct bounded value. -/
theorem evalFabiusDyadic_eq_some_correct (F : BoundedFabius) (hF : IsFabius F)
    (x value : ℚ) (hvalue : evalFabiusDyadic x = some value) :
    (value : ℝ) = fabiusReal F (x : ℝ) := by
  unfold evalFabiusDyadic at hvalue
  split at hvalue
  · simp at hvalue
  · rename_i exponent hexponent
    injection hvalue with hvalue
    subst value
    have hden : x.den = 2 ^ exponent := by
      unfold dyadicExponent? at hexponent
      dsimp only at hexponent
      split at hexponent
      · rename_i h
        injection hexponent with he
        simpa [he] using h
      · simp at hexponent
    rw [fabiusDyadicValue_cast F hF]
    congr 1
    rw [Rat.cast_def, hden]
    norm_num

/-- A successful rational-input evaluation has the correct global value. -/
theorem evalExtendedFabiusDyadic_eq_some_correct
    (F : BoundedFabius) (hF : IsFabius F)
    (x value : ℚ) (hvalue : evalExtendedFabiusDyadic x = some value) :
    (value : ℝ) = extendedFabius F (x : ℝ) := by
  unfold evalExtendedFabiusDyadic at hvalue
  split at hvalue
  · simp at hvalue
  · rename_i exponent hexponent
    injection hvalue with hvalue
    subst value
    have hden : x.den = 2 ^ exponent := by
      unfold dyadicExponent? at hexponent
      dsimp only at hexponent
      split at hexponent
      · rename_i h
        injection hexponent with he
        simpa [he] using h
      · simp at hexponent
    rw [extendedFabiusDyadicValue_cast F hF]
    congr 1
    rw [Rat.cast_def, hden]
    norm_num

/--
Every dyadic rational has an explicitly computed rational value equal to the
bounded analytic Fabius function.
-/
theorem evalFabiusDyadic_complete_correct
    (F : BoundedFabius) (hF : IsFabius F) (x : ℚ)
    (hx : IsDyadicRational x) :
    ∃ value : ℚ,
      evalFabiusDyadic x = some value ∧
        (value : ℝ) = fabiusReal F (x : ℝ) := by
  obtain ⟨exponent, hexponent⟩ := (dyadicExponent?_exists_iff x).2 hx
  let value := fabiusDyadicValue exponent x.num
  have hvalue : evalFabiusDyadic x = some value := by
    simp [evalFabiusDyadic, hexponent, value]
  exact ⟨value, hvalue, evalFabiusDyadic_eq_some_correct F hF x value hvalue⟩

/-- The integer-numerator exact evaluator agrees with Rvachev's function on its support. -/
theorem rvachevDyadic_cast (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (a : ℤ)
    (ha : a.natAbs ≤ 2 ^ n) :
    (rvachevDyadic n a : ℝ) = rvachevUp F (a / (2 : ℝ) ^ n) := by
  sorry

/-- The Fabius-grid and Rvachev-grid descriptions of Definition 12 agree. -/
theorem dyadicDenominator_eq_fabiusDyadicDenominator (n : ℕ) :
    dyadicDenominator n = fabiusDyadicDenominator n := by
  cases n with
  | zero => simp [dyadicDenominator, fabiusDyadicDenominator,
      oddDyadicNumerators]
  | succ n =>
      apply Nat.dvd_antisymm
      · unfold dyadicDenominator fabiusDyadicDenominator
        apply Finset.lcm_dvd
        intro a ha
        have ha_filter := (mem_filter.mp (show
          a ∈ (Finset.Icc 1 (2 ^ (n + 1) - 1)).filter Odd by
            simpa [oddDyadicNumerators] using ha))
        have ha_bounds := Finset.mem_Icc.mp ha_filter.1
        have hascale : a ≤ 2 ^ (n + 1) := by omega
        have hreflect : 2 ^ (n + 1) - a ∈ oddDyadicNumerators (n + 1) :=
          oddDyadicNumerators_reflect_mem (n + 1) a (by omega) ha
        rw [rvachevDyadic, if_pos]
        · exact Finset.dvd_lcm hreflect
        · simpa using hascale
      · unfold dyadicDenominator fabiusDyadicDenominator
        apply Finset.lcm_dvd
        intro a ha
        have ha_filter := (mem_filter.mp (show
          a ∈ (Finset.Icc 1 (2 ^ (n + 1) - 1)).filter Odd by
            simpa [oddDyadicNumerators] using ha))
        have ha_bounds := Finset.mem_Icc.mp ha_filter.1
        let b := 2 ^ (n + 1) - a
        have hbmem : b ∈ oddDyadicNumerators (n + 1) :=
          oddDyadicNumerators_reflect_mem (n + 1) a (by omega) ha
        have hbscale : b ≤ 2 ^ (n + 1) := by
          dsimp [b]
          omega
        have hba : 2 ^ (n + 1) - b = a := by
          dsimp [b]
          omega
        have hdvd := Finset.dvd_lcm (f := fun c : ℕ =>
          (rvachevDyadic (n + 1) c).den) hbmem
        rw [rvachevDyadic, if_pos] at hdvd
        · simpa [b, hba] using hdvd
        · simpa using hbscale

/-- The exact `R_n` is the paper's analytic expression after coercion to `ℝ`. -/
theorem reshetnikov_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    (reshetnikov n : ℝ) =
      (2 : ℝ) ^ (n - 1).choose 2 * (Nat.factorial (2 * n) : ℝ) *
        fabiusReal F (((2 : ℝ) ^ n)⁻¹) * evenMersenneProduct (n / 2) := by
  unfold reshetnikov fabiusAtInverseTwoPow
  push_cast
  rw [fabiusDyadic_cast F hF n 1 Nat.one_le_two_pow]
  congr 3
  norm_num

/-! ## Numbered results -/

/-- Proposition 1: recurrence and natural normalization of the moments `c_n`. -/
theorem proposition_one :
    moment 0 = 1 ∧
    (∀ n : ℕ, 1 ≤ n →
      (((2 * n + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * n) - 1) * moment n =
        (∑ k ∈ range n,
          (Nat.choose (2 * n + 1) (2 * k) : ℚ) * moment k))) ∧
    (∀ n : ℕ,
      moment n =
        (momentNumerator n : ℚ) /
          ((oddDoubleFactorial (n + 1) * evenMersenneProduct n : ℕ) : ℚ)) := by
  sorry

/-- Proposition 2: the functional equation for the entire generating function. -/
theorem proposition_two (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F (2 * z) =
      complexExpm1Div z * complexGeneratingFunction F z := by
  sorry

/-- The real restriction of Proposition 2. -/
theorem proposition_two_real (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    generatingFunction F (2 * x) = expm1Div x * generatingFunction F x := by
  sorry

/-- Proposition 3: the half moments in terms of the even moments. -/
theorem proposition_three (n : ℕ) :
    halfMoment n =
      (∑ k ∈ range (n / 2 + 1),
        (Nat.choose n (2 * k) : ℚ) * moment k) / (2 : ℚ) ^ n := by
  exact halfMoment_eq_evenMomentSum n

/-- Proposition 4: the natural normalization `G_n` of the half moments. -/
theorem proposition_four (n : ℕ) :
    halfMoment n =
      (halfMomentNumerator n : ℚ) /
        (((n + 1).factorial * mersenneProduct n : ℕ) : ℚ) := by
  exact halfMoment_eq_halfMomentNumerator n

/-- Question 5 (Reshetnikov), subsequently answered by Theorem 9. -/
def reshetnikovQuestion : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsNatural (reshetnikov n)

/-- Proposition 6: `R_n` in terms of `d_n`. -/
theorem proposition_six (n : ℕ) (hn : 1 ≤ n) :
    reshetnikov n =
      2 * halfMoment n * oddDoubleFactorial n * evenMersenneProduct (n / 2) := by
  rw [reshetnikov, fabiusAtInverseTwoPow_eq_halfMoment,
    halfMomentFabiusValue, factorial_two_mul_eq]
  have hexp : (n - 1).choose 2 + n = n.choose 2 + 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 1 + m - 1 = m by omega]
    rw [show 1 + m = m + 1 by omega]
    rw [show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
    simp [Nat.choose_one_right]
    omega
  push_cast
  field_simp
  rw [← pow_add, hexp, pow_succ]
  ring

/-- Theorem 7: the exact odd-index formula, hence divisibility by `F_n`. -/
theorem theorem_seven (n : ℕ) :
    reshetnikov (2 * n + 1) =
      (momentNumerator n : ℚ) *
        (∏ j ∈ Icc n (2 * n), ((2 * j + 1 : ℕ) : ℚ)) ∧
    IsNatural (reshetnikov (2 * n + 1)) ∧
    (∃ m : ℕ,
      reshetnikov (2 * n + 1) = (momentNumerator n * m : ℕ)) := by
  sorry

/-- Proposition 8: the even-index formula and its power-of-two denominator bound. -/
theorem proposition_eight (n : ℕ) (hn : 1 ≤ n) :
    reshetnikov (2 * n) =
      ∑ k : Fin (n + 1),
        (2 * (momentNumerator k.val : ℚ) * Nat.choose (2 * n) (2 * k.val) *
          oddFactorProduct (k.val + 1) (2 * n) *
          (∏ ell ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * ell) - 1))) /
            (2 : ℚ) ^ (2 * n) ∧
    (reshetnikov (2 * n)).den ∣ 2 ^ (2 * n) := by
  sorry

/-- Theorem 9: Reshetnikov's numbers are natural numbers. -/
theorem theorem_nine (n : ℕ) (hn : 1 ≤ n) :
    IsNatural (reshetnikov n) := by
  sorry

/--
Lemma 1, with the missing hypothesis from the printed paper restored.
Without `horder`, the statement is false when `scale` is negative.
-/
theorem lemma_one (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (scale : ℤ) (order : ℕ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ scale ≤ x)
    (hhi : x < (2 : ℝ) ^ (scale + 1))
    (horder : (0 : ℤ) ≤ scale + order) :
    (∫ t in (2 : ℝ) ^ scale..x,
        (x - t) ^ order * iteratedDeriv (order + 1) (extendedFabius F) t) =
      -(∫ t in 0..(x - (2 : ℝ) ^ scale),
        (x - (2 : ℝ) ^ scale - t) ^ order *
          iteratedDeriv (order + 1) (extendedFabius F) t) := by
  sorry

/-- The finite Taylor sum in Proposition 10 when its integer index is nonnegative. -/
def fabiusReductionSum (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (2 : ℝ) ^ ((Nat.choose (k + 1) 2 : ℤ) - Nat.choose (n - k) 2) *
      (halfMoment (n - k) : ℝ) / (n - k).factorial * y ^ k / k.factorial

/-- Proposition 10: the recursive evaluation formula for the signed extension. -/
theorem proposition_ten (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) (n : ℤ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ (-n) ≤ x)
    (hhi : x < (2 : ℝ) ^ (-n + 1)) :
    let y := x - (2 : ℝ) ^ (-n)
    extendedFabius F x = -extendedFabius F y +
      if 0 ≤ n then fabiusReductionSum n.toNat y else 0 := by
  sorry

/-
Definition 12 is `dyadicDenominator` in `Arithmetic.lean`: the LCM of the
reduced denominators on the positive odd level-`n` dyadic grid.
-/

/-- Theorem 13: a common integral scaling of all level-`n` dyadic values. -/
theorem theorem_thirteen (n : ℕ) (hn : 1 ≤ n) (a : ℤ)
    (haLower : -((2 ^ n : ℕ) : ℤ) < a)
    (haUpper : a < ((2 ^ n : ℕ) : ℤ)) :
    IsNatural (rvachevDyadic n a * denominatorBound n) := by
  sorry

/-- The common-denominator formulation following Theorem 13. -/
theorem theorem_thirteen_denominator_bound (n : ℕ) (hn : 1 ≤ n) :
    dyadicDenominator n ∣ denominatorBound n := by
  sorry

/-- Proposition 15: the denominator at `2⁻ⁿ` divides the common denominator. -/
theorem proposition_fifteen (n : ℕ) :
    (halfMomentFabiusValue n).den ∣ dyadicDenominator n := by
  rw [dyadicDenominator_eq_fabiusDyadicDenominator]
  by_cases hn : n = 0
  · subst n
    norm_num [halfMomentFabiusValue, fabiusDyadicDenominator]
  · rw [← fabiusAtInverseTwoPow_eq_halfMoment]
    unfold fabiusAtInverseTwoPow fabiusDyadicDenominator
    apply Finset.dvd_lcm
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpow : 1 < 2 ^ n := one_lt_pow₀ (by omega) hn
    have hone : 1 ≤ 2 ^ n - 1 := by omega
    simp [oddDyadicNumerators, hone]

/--
Conjecture 16.  Natural divisibility is expressed through an explicit natural
quotient, rather than `∣` in `ℚ` (where divisibility would be trivial).
-/
def conjecture_sixteen : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    normalizedDyadicDenominator (2 * n) =
      normalizedDyadicDenominator (2 * n + 1)) ∧
  (∀ n : ℕ, 2 ≤ n →
    conjecturalK n = normalizedDyadicDenominator (2 * n - 2)) ∧
  (∀ n : ℕ, 1 ≤ n →
    ∃ q : ℕ, conjecturalK n = (2 * (2 * n - 1).factorial * q : ℕ)) ∧
  (∀ n : ℕ, 1 ≤ n → IsOddNatural (conjecturalH n))

/-- Theorem 17: Lucas's theorem in the digit-product form used by the paper. -/
theorem theorem_seventeen (p n k a : ℕ) (hp : p.Prime)
    (hn : n < p ^ (a + 1)) (hk : k < p ^ (a + 1)) :
    Nat.ModEq p (Nat.choose n k)
      (∏ i ∈ range (a + 1),
        Nat.choose (n / p ^ i % p) (k / p ^ i % p)) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact Choose.lucas_theorem_nat hn hk

/-- Proposition 18: counts of the odd binomial coefficients in the two ranges. -/
theorem proposition_eighteen (n : ℕ) (hn : 1 ≤ n) :
    ((range (n + 1)).filter
      (fun k => Odd (Nat.choose (2 * n + 1) (2 * k)))).card =
        2 ^ binaryWeight n ∧
    ((range (2 * n + 2)).filter
      (fun k => Odd (Nat.choose (2 * n + 1) k))).card =
        2 ^ (binaryWeight n + 1) := by
  sorry

/-- Proposition 19: every natural moment numerator `F_n` is odd. -/
theorem proposition_nineteen (n : ℕ) :
    Odd (momentNumerator n) := by
  sorry

/-- Theorem 20: the numerator and denominator of `2 d_n` are odd. -/
theorem theorem_twenty (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (2 * halfMoment n) = 0 ∧
      Odd (2 * halfMoment n).num.natAbs ∧ Odd (2 * halfMoment n).den := by
  sorry

/-- Theorem 21: oddness of `R_n` and the exact dyadic valuation. -/
theorem theorem_twenty_one (n : ℕ) (hn : 1 ≤ n) :
    IsOddNatural (reshetnikov n) ∧
    padicValRat 2 (fabiusAtInverseTwoPow n) =
      -(n.choose 2 : ℤ) - 1 - padicValRat 2 (n.factorial : ℚ) := by
  sorry

/-- Proposition 22: the Bernoulli recurrences for `c_n` and `d_n`. -/
theorem proposition_twenty_two_initial : moment 0 = 1 ∧ halfMoment 0 = 1 := by
  simp

theorem proposition_twenty_two (n : ℕ) (hn : 1 ≤ n) :
    moment n =
      (∑ k ∈ Icc 1 n,
        (2 : ℚ) ^ (2 * n - 2 * k) * ((2 : ℚ) ^ (2 * k) - 2) *
          Nat.choose (2 * n) (2 * k) * bernoulli (2 * k) * moment (n - k)) /
        ((2 : ℚ) ^ (2 * n) - 1) ∧
    halfMoment n =
      ((n : ℚ) * (2 : ℚ) ^ n / (4 * ((2 : ℚ) ^ n - 1))) *
          halfMoment (n - 1) -
        (∑ k ∈ Icc 1 (n / 2),
          (Nat.choose n (2 * k) : ℚ) * (2 : ℚ) ^ (n - 2 * k) *
            bernoulli (2 * k) * halfMoment (n - 2 * k)) /
          ((2 : ℚ) ^ n - 1) := by
  sorry

end

end Fabius
