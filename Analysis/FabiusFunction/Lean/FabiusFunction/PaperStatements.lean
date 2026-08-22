import FabiusFunction.Basic
import FabiusFunction.DyadicCorrectness
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

/-- The bounded/CDF Fabius function is monotone on all of `ℝ`. -/
theorem fabius_monotone (F : BoundedFabius) (hF : IsFabius F) :
    Monotone (fabiusReal F) := by
  sorry

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
  sorry

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

/-- Equation (9), the original recurrence before isolating `c_n`. -/
theorem moment_original_recurrence (n : ℕ) :
    ((2 * n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * n) * moment n =
      ∑ k ∈ range (n + 1),
        (Nat.choose (2 * n + 1) (2 * k) : ℚ) * moment k := by
  cases n with
  | zero => norm_num
  | succ n =>
      rw [sum_range_succ]
      have hsum :
          (∑ k : Fin (n + 1),
              (Nat.choose (2 * (n + 1) + 1) (2 * k.val) : ℚ) * moment k.val) =
            ∑ k ∈ range (n + 1),
              (Nat.choose (2 * (n + 1) + 1) (2 * k) : ℚ) * moment k := by
        simpa using (Fin.sum_univ_eq_sum_range
          (fun k : ℕ =>
            (Nat.choose (2 * (n + 1) + 1) (2 * k) : ℚ) * moment k) (n + 1))
      have hpow : (1 : ℚ) < 2 ^ (2 * (n + 1)) := by
        exact one_lt_pow₀ (by norm_num) (by omega)
      have hden : ((((2 * (n + 1) + 1 : ℕ) : ℚ) *
          ((2 : ℚ) ^ (2 * (n + 1)) - 1))) ≠ 0 :=
        mul_ne_zero (by positivity) (ne_of_gt (sub_pos.mpr hpow))
      have hrec := (eq_div_iff hden).mp (moment_succ n)
      rw [hsum] at hrec
      have hchoose : Nat.choose (2 * (n + 1) + 1) (2 * (n + 1)) =
          2 * (n + 1) + 1 := by
        convert Nat.choose_succ_self_right (2 * (n + 1)) using 1
      rw [hchoose]
      push_cast at hrec ⊢
      linear_combination hrec

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

/-- The two exact definitions of `F(2⁻ⁿ)` agree. -/
theorem fabiusAtInverseTwoPow_eq_halfMoment (n : ℕ) :
    fabiusAtInverseTwoPow n = halfMomentFabiusValue n := by
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

/-- The total signed-numerator evaluator computes the bounded Fabius function. -/
theorem fabiusDyadicValue_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (a : ℤ) :
    (fabiusDyadicValue n a : ℝ) =
      fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) := by
  sorry

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
  sorry

/-- A successful rational-input evaluation has the correct global value. -/
theorem evalExtendedFabiusDyadic_eq_some_correct
    (F : BoundedFabius) (hF : IsFabius F)
    (x value : ℚ) (hvalue : evalExtendedFabiusDyadic x = some value) :
    (value : ℝ) = extendedFabius F (x : ℝ) := by
  sorry

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

/-- The integer-numerator exact evaluator agrees with Rvachev's function on its support. -/
theorem rvachevDyadic_cast (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (a : ℤ)
    (ha : a.natAbs ≤ 2 ^ n) :
    (rvachevDyadic n a : ℝ) = rvachevUp F (a / (2 : ℝ) ^ n) := by
  sorry

/-- The Fabius-grid and Rvachev-grid descriptions of Definition 12 agree. -/
theorem dyadicDenominator_eq_fabiusDyadicDenominator (n : ℕ) :
    dyadicDenominator n = fabiusDyadicDenominator n := by
  sorry

/-- The exact `R_n` is the paper's analytic expression after coercion to `ℝ`. -/
theorem reshetnikov_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    (reshetnikov n : ℝ) =
      (2 : ℝ) ^ (n - 1).choose 2 * (Nat.factorial (2 * n) : ℝ) *
        fabiusReal F (((2 : ℝ) ^ n)⁻¹) * evenMersenneProduct (n / 2) := by
  sorry

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
  sorry

/-- Proposition 4: the natural normalization `G_n` of the half moments. -/
theorem proposition_four (n : ℕ) :
    halfMoment n =
      (halfMomentNumerator n : ℚ) /
        (((n + 1).factorial * mersenneProduct n : ℕ) : ℚ) := by
  sorry

/-- Question 5 (Reshetnikov), subsequently answered by Theorem 9. -/
def reshetnikovQuestion : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsNatural (reshetnikov n)

/-- Proposition 6: `R_n` in terms of `d_n`. -/
theorem proposition_six (n : ℕ) (hn : 1 ≤ n) :
    reshetnikov n =
      2 * halfMoment n * oddDoubleFactorial n * evenMersenneProduct (n / 2) := by
  sorry

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
  sorry

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
  sorry

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
