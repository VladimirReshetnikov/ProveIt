import GowersSzemeredi.Section05
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Nat.Dist
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Weyl's inequality

This file supplies the proof of Lemma 5.3.  We keep the exponential phase
as a real number (rather than immediately quotienting by `ℤ`) because this
is the form used by the statement, but use `UnitAddCircle` whenever distance
to the nearest integer is involved.

The quantitative proof follows the finite Weyl-differencing argument.  In
particular, all sums below are genuinely finite; no equidistribution or
asymptotic result is used as an additional assumption.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma realExponential_norm (x : Real) :
    ‖realExponential x‖ = 1 := by
  simpa [realExponential, mul_assoc] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

private lemma realExponential_add (x y : Real) :
    realExponential (x + y) = realExponential x * realExponential y := by
  simp only [realExponential]
  rw [show (2 * Real.pi * (x + y) : Real) =
      2 * Real.pi * x + 2 * Real.pi * y by ring]
  push_cast
  rw [add_mul, Complex.exp_add]

private lemma realExponential_neg (x : Real) :
    realExponential (-x) = (realExponential x)⁻¹ := by
  unfold realExponential
  rw [show ((((2 * Real.pi * -x : Real) : Complex) * Complex.I)) =
      -((((2 * Real.pi * x : Real) : Complex) * Complex.I)) by
        push_cast
        ring]
  exact Complex.exp_neg _

private lemma realExponential_sub (x y : Real) :
    realExponential (x - y) = realExponential x * (realExponential y)⁻¹ := by
  rw [sub_eq_add_neg, realExponential_add, realExponential_neg]

private lemma realExponential_nat_mul (x : Real) (n : Nat) :
    realExponential (n * x) = (realExponential x) ^ n := by
  induction n with
  | zero => simp [realExponential]
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, realExponential_add, ih, pow_succ, one_mul]

private lemma realExponential_intCast (n : Int) :
    realExponential (n : Real) = 1 := by
  calc
    realExponential (n : Real) =
        Complex.exp ((n : Complex) * (2 * Real.pi * Complex.I)) := by
      unfold realExponential
      congr 1
      push_cast
      ring
    _ = 1 := Complex.exp_int_mul_two_pi_mul_I n

private lemma realExponential_sub_round (x : Real) :
    realExponential (x - round x) = realExponential x := by
  rw [realExponential_sub, realExponential_intCast]
  simp

private lemma star_realExponential (x : Real) :
    star (realExponential x) = realExponential (-x) := by
  unfold realExponential
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-! The denominator estimate underlying the finite geometric-sum bound. -/

private lemma realExponential_denominator_lower_bound (x : Real) :
    4 * ‖(x : UnitAddCircle)‖ ≤ ‖realExponential x - 1‖ := by
  let y : Real := x - round x
  have hyabs : |y| = ‖(x : UnitAddCircle)‖ := by
    rw [UnitAddCircle.norm_eq]
  have hyle : |y| ≤ (2 : Real)⁻¹ := by
    simpa [one_div, y] using (abs_sub_round x)
  have hpi : |Real.pi * y| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left hyle Real.pi_pos.le)
  have hjordan : 2 / Real.pi * |Real.pi * y| ≤ |Real.sin (Real.pi * y)| :=
    Real.mul_abs_le_abs_sin hpi
  rw [← realExponential_sub_round x]
  unfold realExponential
  rw [show (((2 * Real.pi * y : Real) : Complex) * Complex.I) =
      Complex.I * ((2 * Real.pi * y : Real) : Complex) by ring,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * y / 2 = Real.pi * y by ring]
  change 4 * ‖(x : UnitAddCircle)‖ ≤ ‖(2 : Real) * Real.sin (Real.pi * y)‖
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2), ← hyabs]
  calc
    4 * |y| = 2 * (2 / Real.pi * |Real.pi * y|) := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_ne_zero]
      <;> ring
    _ ≤ 2 * |Real.sin (Real.pi * y)| := by gcongr

/-- The convention `min(n, ‖x‖⁻¹ / 2)` for a geometric sum, with the
integer-frequency case assigned its correct value `n` instead of Lean's
`0⁻¹ = 0`. -/
private def geometricSumMajorant (n : Nat) (x : Real) : Real :=
  if (x : UnitAddCircle) = 0 then n
  else min n (2 * ‖(x : UnitAddCircle)‖)⁻¹

private lemma geometricSumMajorant_nonneg (n : Nat) (x : Real) :
    0 ≤ geometricSumMajorant n x := by
  unfold geometricSumMajorant
  split_ifs
  · positivity
  · exact le_min (by positivity)
      (inv_nonneg.mpr (mul_nonneg (by norm_num) (norm_nonneg _)))

private lemma norm_sum_linear_phase_le (x c : Real) (n : Nat) :
    ‖∑ s ∈ range n, realExponential (x * s + c)‖ ≤
      geometricSumMajorant n x := by
  have hfactor :
      (∑ s ∈ range n, realExponential (x * s + c)) =
        realExponential c * ∑ s ∈ range n, (realExponential x) ^ s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by
      rw [← realExponential_nat_mul, ← realExponential_add]; ring_nf
  have htriv : ‖∑ s ∈ range n, (realExponential x) ^ s‖ ≤ n :=
    (norm_sum_le _ _).trans (by simp [realExponential_norm])
  rw [hfactor, norm_mul, realExponential_norm, one_mul]
  unfold geometricSumMajorant
  split_ifs with hx
  · exact htriv
  have hnorm : 0 < ‖(x : UnitAddCircle)‖ := norm_pos_iff.mpr hx
  have hlower := realExponential_denominator_lower_bound x
  have hphase : realExponential x ≠ 1 := fun h => by
    rw [h, sub_self, norm_zero] at hlower
    linarith
  have hnum : ‖realExponential x ^ n - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_pow, realExponential_norm]; norm_num)
  refine le_min htriv ?_
  rw [geom_sum_eq hphase, norm_div, div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hphase)),
    inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith [mul_le_mul_of_nonneg_right hnum hnorm.le]

private lemma geometricSumMajorant_mono {m n : Nat} (hmn : m ≤ n) (x : Real) :
    geometricSumMajorant m x ≤ geometricSumMajorant n x := by
  unfold geometricSumMajorant
  split_ifs
  · exact_mod_cast hmn
  · exact min_le_min_right _ (by exact_mod_cast hmn)

private lemma norm_sum_linear_phase_Icc_le (x c : Real) (a b : Int) :
    ‖∑ s ∈ Icc a b, realExponential (x * (s : Real) + c)‖ ≤
      geometricSumMajorant (Icc a b).card x := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  have h := norm_sum_linear_phase_le x (x * (a : Real) + c)
    (b + 1 - a).toNat
  simpa only [Int.card_Icc, Finset.card_map, Finset.card_range,
    Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, Int.cast_natCast,
    Int.cast_add, mul_add, add_assoc, add_left_comm] using h

private lemma weylSum_norm_le (alpha : Real) (k t : Nat) :
    ‖weylSum alpha k t‖ ≤ t := by
  unfold weylSum
  calc
    ‖∑ s ∈ Icc 1 t, realExponential (alpha * (s : Real) ^ k)‖ ≤
        ∑ s ∈ Icc 1 t, ‖realExponential (alpha * (s : Real) ^ k)‖ :=
      norm_sum_le _ _
    _ = (Icc 1 t).card := by simp [realExponential_norm]
    _ = t := by simp [Nat.card_Icc]

/-! ## Finite correlations

This is the algebraic core of Weyl differencing.  It is stated for an
arbitrary finite set and a finite set containing all of its differences, so
later iterations can use one fixed ambient range of shifts even though the
actual interval shrinks.
-/

private def finiteCorrelation (s : Finset Int) (f : Int → Complex) (h : Int) :
    Complex :=
  ∑ x ∈ s.filter (fun x => x + h ∈ s), f (x + h) * star (f x)

private lemma sum_difference_fiber_eq_correlation
    (s : Finset Int) (f : Int → Complex) (h : Int) :
    (∑ p ∈ (s ×ˢ s).filter (fun p => p.1 - p.2 = h),
        f p.1 * star (f p.2)) = finiteCorrelation s f h := by
  symm
  unfold finiteCorrelation
  apply Finset.sum_bij (fun x _ => (x + h, x))
  · intro x hx
    obtain ⟨hxS, hxhS⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hxhS, hxS⟩, by omega⟩
  · intro x₁ _ x₂ _ heq
    exact congrArg Prod.snd heq
  · intro p hp
    obtain ⟨hpS, hpDiff⟩ := mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := mem_product.mp hpS
    refine ⟨p.2, mem_filter.mpr ⟨hp2, ?_⟩, ?_⟩
    · rw [← hpDiff]
      have hadd : p.2 + (p.1 - p.2) = p.1 := by omega
      simpa only [hadd] using hp1
    · apply Prod.ext
      · omega
      · rfl
  · intro x _
    rfl

private lemma sum_mul_star_sum_eq_sum_correlation
    (s d : Finset Int) (f : Int → Complex)
    (hd : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ d) :
    (∑ x ∈ s, f x) * star (∑ y ∈ s, f y) =
      ∑ h ∈ d, finiteCorrelation s f h := by
  have hmaps : ∀ p ∈ s ×ˢ s, p.1 - p.2 ∈ d := by
    intro p hp
    exact hd p.1 (mem_product.mp hp).1 p.2 (mem_product.mp hp).2
  calc
    (∑ x ∈ s, f x) * star (∑ y ∈ s, f y) =
        ∑ x ∈ s, ∑ y ∈ s, f x * star (f y) := by
      simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ p ∈ s ×ˢ s, f p.1 * star (f p.2) :=
      (Finset.sum_product' s s (fun x y => f x * star (f y))).symm
    _ = ∑ h ∈ d, ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 - p.2 = h),
          f p.1 * star (f p.2) := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ h ∈ d, finiteCorrelation s f h := by
      refine Finset.sum_congr rfl fun h _ => ?_
      exact sum_difference_fiber_eq_correlation s f h

private lemma norm_sum_sq_le_sum_norm_correlation
    (s d : Finset Int) (f : Int → Complex)
    (hd : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ d) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ ∑ h ∈ d, ‖finiteCorrelation s f h‖ := by
  let S : Complex := ∑ x ∈ s, f x
  have hcorr := sum_mul_star_sum_eq_sum_correlation s d f hd
  change ‖S‖ ^ 2 ≤ _
  calc
    ‖S‖ ^ 2 = ‖S * star S‖ := by simp [pow_two]
    _ = ‖∑ h ∈ d, finiteCorrelation s f h‖ := by rw [hcorr]
    _ ≤ ∑ h ∈ d, ‖finiteCorrelation s f h‖ := norm_sum_le _ _

/-! The shrinking interval and phase after a list of signed differences. -/

private def differenceBounds (a b : Int) : List Int → Int × Int
  | [] => (a, b)
  | h :: hs =>
      let old := differenceBounds a b hs
      (max old.1 (old.1 - h), min old.2 (old.2 - h))

private def iteratedRealDifference (phi : Int → Real) : List Int → Int → Real
  | [], x => phi x
  | h :: hs, x =>
      iteratedRealDifference phi hs (x + h) - iteratedRealDifference phi hs x

private def finiteDifferenceSum (phi : Int → Real) (a b : Int)
    (hs : List Int) : Complex :=
  let bounds := differenceBounds a b hs
  ∑ x ∈ Icc bounds.1 bounds.2,
    realExponential (iteratedRealDifference phi hs x)

private lemma differenceBounds_interval_subset (a b : Int) (hs : List Int) :
    Icc (differenceBounds a b hs).1 (differenceBounds a b hs).2 ⊆ Icc a b := by
  induction hs with
  | nil => simp [differenceBounds]
  | cons h hs ih =>
      intro x hx
      apply ih
      rw [mem_Icc] at hx ⊢
      dsimp only [differenceBounds] at hx
      exact ⟨hx.1.trans' (le_max_left _ _), hx.2.trans (min_le_left _ _)⟩

private lemma filter_interval_add_mem (a b h : Int) :
    (Icc a b).filter (fun x => x + h ∈ Icc a b) =
      Icc (max a (a - h)) (min b (b - h)) := by
  ext x
  simp only [mem_filter, mem_Icc]
  omega

private lemma finiteCorrelation_realExponential_interval
    (phi : Int → Real) (a b h : Int) :
    finiteCorrelation (Icc a b) (fun x => realExponential (phi x)) h =
      ∑ x ∈ Icc (max a (a - h)) (min b (b - h)),
        realExponential (phi (x + h) - phi x) := by
  unfold finiteCorrelation
  rw [filter_interval_add_mem]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [star_realExponential, ← realExponential_add]
  congr 1

private lemma finiteCorrelation_finiteDifferenceSum
    (phi : Int → Real) (a b h : Int) (hs : List Int) :
    finiteCorrelation
        (Icc (differenceBounds a b hs).1 (differenceBounds a b hs).2)
        (fun x => realExponential (iteratedRealDifference phi hs x)) h =
      finiteDifferenceSum phi a b (h :: hs) := by
  rw [finiteCorrelation_realExponential_interval]
  rfl

private def weylShiftRange (t : Nat) : Finset Int :=
  Ioo (-(t : Int)) (t : Int)

private lemma sub_mem_weylShiftRange {t : Nat} {x y : Int}
    (hx : x ∈ Icc (1 : Int) t) (hy : y ∈ Icc (1 : Int) t) :
    x - y ∈ weylShiftRange t := by
  rw [mem_Icc] at hx hy
  rw [weylShiftRange, mem_Ioo]
  constructor <;> omega

private lemma weylShiftRange_card_le (t : Nat) :
    (weylShiftRange t).card ≤ 2 * t := by
  rw [weylShiftRange, Int.card_Ioo]
  omega

private lemma finiteDifferenceSum_sq_le
    (phi : Int → Real) (t : Nat) (hs : List Int) :
    ‖finiteDifferenceSum phi 1 t hs‖ ^ 2 ≤
      ∑ h ∈ weylShiftRange t,
        ‖finiteDifferenceSum phi 1 t (h :: hs)‖ := by
  let bounds := differenceBounds 1 t hs
  let s : Finset Int := Icc bounds.1 bounds.2
  have hsSubset : s ⊆ Icc (1 : Int) t := differenceBounds_interval_subset 1 t hs
  have hd : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ weylShiftRange t := by
    intro x hx y hy
    exact sub_mem_weylShiftRange (hsSubset hx) (hsSubset hy)
  have hcorr := norm_sum_sq_le_sum_norm_correlation s (weylShiftRange t)
    (fun x => realExponential (iteratedRealDifference phi hs x)) hd
  change ‖finiteDifferenceSum phi 1 t hs‖ ^ 2 ≤ _
  simpa only [finiteDifferenceSum, bounds, s,
    finiteCorrelation_finiteDifferenceSum] using hcorr

/-!
Repeated differencing is best organized using two recursively nested sums.
`iteratedDifferenceNormSum j hs` sums the norms after adjoining `j` more
shifts, while `iteratedDifferenceNormSqSum` sums their squares.  Keeping the
nesting explicit avoids any quotienting or choice of representatives for
shift tuples.
-/

private def iteratedDifferenceNormSum (phi : Int → Real) (t : Nat) :
    Nat → List Int → Real
  | 0, hs => ‖finiteDifferenceSum phi 1 t hs‖
  | j + 1, hs =>
      ∑ h ∈ weylShiftRange t, iteratedDifferenceNormSum phi t j (h :: hs)

private def iteratedDifferenceNormSqSum (phi : Int → Real) (t : Nat) :
    Nat → List Int → Real
  | 0, hs => ‖finiteDifferenceSum phi 1 t hs‖ ^ 2
  | j + 1, hs =>
      ∑ h ∈ weylShiftRange t, iteratedDifferenceNormSqSum phi t j (h :: hs)

private lemma iteratedDifferenceNormSum_sq_le (phi : Int → Real) (t j : Nat)
    (hs : List Int) :
    iteratedDifferenceNormSum phi t j hs ^ 2 ≤
      (weylShiftRange t).card ^ j *
        iteratedDifferenceNormSqSum phi t j hs := by
  induction j generalizing hs with
  | zero => simp [iteratedDifferenceNormSum, iteratedDifferenceNormSqSum]
  | succ j ih =>
      simp only [iteratedDifferenceNormSum, iteratedDifferenceNormSqSum]
      refine sq_sum_le_card_mul_sum_sq.trans ?_
      rw [pow_succ' _ j, mul_assoc]
      gcongr
      rw [Finset.mul_sum]
      gcongr with h _
      exact ih (h :: hs)

private lemma iteratedDifferenceNormSqSum_le_succ
    (phi : Int → Real) (t j : Nat) (hs : List Int) :
    iteratedDifferenceNormSqSum phi t j hs ≤
      iteratedDifferenceNormSum phi t (j + 1) hs := by
  induction j generalizing hs with
  | zero =>
      simpa [iteratedDifferenceNormSqSum, iteratedDifferenceNormSum] using
        finiteDifferenceSum_sq_le phi t hs
  | succ j ih =>
      simp only [iteratedDifferenceNormSqSum, iteratedDifferenceNormSum]
      gcongr with h _
      exact ih (h :: hs)

/-- The exponent of the ambient shift-range cardinality after `j` exact
Cauchy--Schwarz steps.  Its closed form is `2^j - j - 1`. -/
private def weylCauchyExponent : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * weylCauchyExponent j + j

lemma nat_succ_le_two_pow (e : Nat) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      calc
        e + 1 + 1 ≤ 2 * (e + 1) := by omega
        _ ≤ 2 * 2 ^ e := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (e + 1) := by rw [pow_succ']

private lemma weylCauchyExponent_eq (j : Nat) :
    weylCauchyExponent j = 2 ^ j - j - 1 := by
  induction j with
  | zero => simp [weylCauchyExponent]
  | succ j ih =>
      rw [weylCauchyExponent, ih, pow_succ]
      have hj := nat_succ_le_two_pow j
      omega

private lemma finiteDifferenceSum_iterated_le (phi : Int → Real) (t j : Nat)
    (hs : List Int) :
    ‖finiteDifferenceSum phi 1 t hs‖ ^ (2 ^ j) ≤
      (weylShiftRange t).card ^ weylCauchyExponent j *
        iteratedDifferenceNormSum phi t j hs := by
  induction j generalizing hs with
  | zero => simp [iteratedDifferenceNormSum, weylCauchyExponent]
  | succ j ih =>
      calc
        ‖finiteDifferenceSum phi 1 t hs‖ ^ (2 ^ (j + 1)) =
            (‖finiteDifferenceSum phi 1 t hs‖ ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
        _ ≤ ((weylShiftRange t).card ^ weylCauchyExponent j *
              iteratedDifferenceNormSum phi t j hs) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (ih hs) 2
        _ ≤ (((weylShiftRange t).card : Real) ^ weylCauchyExponent j) ^ 2 *
              ((weylShiftRange t).card ^ j * iteratedDifferenceNormSum phi t (j + 1) hs) := by
          rw [mul_pow]
          gcongr
          exact (iteratedDifferenceNormSum_sq_le phi t j hs).trans
            (by gcongr; exact iteratedDifferenceNormSqSum_le_succ phi t j hs)
        _ = _ := by simp only [weylCauchyExponent, pow_add]; ring

/-! ## The terminal linear phase

The following elementary development is for *arbitrary* signed increments.
Mathlib's `fwdDiff_iter_eq_factorial` treats repeated unit increments; the
mixed-increment version needed here is proved from the binomial theorem.  We
simultaneously prove that too many differences annihilate a monomial.  This
makes the disappearance of all lower binomial terms completely explicit.
-/

private def realShiftProduct (hs : List Int) : Real :=
  (hs.map fun h => (h : Real)).prod

private lemma iteratedRealDifference_append_singleton (f : Int → Real)
    (hs : List Int) (h x : Int) :
    iteratedRealDifference f (hs ++ [h]) x =
      iteratedRealDifference (fun y => f (y + h) - f y) hs x := by
  induction hs generalizing x with
  | nil => rfl
  | cons a hs ih =>
      simp only [List.cons_append, iteratedRealDifference]
      rw [ih, ih]

private lemma iteratedRealDifference_smul (c : Real) (f : Int → Real)
    (hs : List Int) (x : Int) :
    iteratedRealDifference (fun y => c * f y) hs x =
      c * iteratedRealDifference f hs x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      simp only [iteratedRealDifference]
      rw [ih, ih]
      ring

private lemma iteratedRealDifference_finsetSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Int → Real) (hs : List Int) (x : Int) :
    iteratedRealDifference (fun y => ∑ i ∈ s, f i y) hs x =
      ∑ i ∈ s, iteratedRealDifference (f i) hs x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      simp only [iteratedRealDifference]
      rw [ih, ih, Finset.sum_sub_distrib]

private lemma forwardDifference_pow_eq (k : Nat) (h : Int) :
    (fun x : Int => ((x + h : Int) : Real) ^ k - (x : Real) ^ k) =
      fun x : Int => ∑ i ∈ range k,
        (((k.choose i : Nat) : Real) * (h : Real) ^ (k - i)) *
          (x : Real) ^ i := by
  funext x
  rw [Int.cast_add, add_pow, sum_range_succ]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
  rw [add_sub_cancel_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma iteratedRealDifference_pow_eq_zero_of_lt (hs : List Int)
    {j : Nat} (hj : j < hs.length) (x : Int) :
    iteratedRealDifference (fun y => (y : Real) ^ j) hs x = 0 := by
  induction hs using List.reverseRecOn generalizing j x with
  | nil => simp at hj
  | append_singleton hs h ih =>
      rw [iteratedRealDifference_append_singleton, forwardDifference_pow_eq]
      rw [iteratedRealDifference_finsetSum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [iteratedRealDifference_smul]
      have hiJ : i < j := mem_range.mp hi
      have hiLen : i < hs.length := by
        have hj' : j < hs.length + 1 := by
          simpa only [List.length_append, List.length_singleton] using hj
        omega
      rw [ih hiLen, mul_zero]

private lemma realShiftProduct_append_singleton (hs : List Int) (h : Int) :
    realShiftProduct (hs ++ [h]) = realShiftProduct hs * (h : Real) := by
  induction hs with
  | nil => simp [realShiftProduct]
  | cons a hs ih =>
      change (a : Real) * realShiftProduct (hs ++ [h]) =
        ((a : Real) * realShiftProduct hs) * (h : Real)
      rw [ih]
      ring

private lemma iteratedRealDifference_pow_length (hs : List Int) (x : Int) :
    iteratedRealDifference (fun y => (y : Real) ^ hs.length) hs x =
      (Nat.factorial hs.length : Real) * realShiftProduct hs := by
  induction hs using List.reverseRecOn generalizing x with
  | nil => simp [iteratedRealDifference, realShiftProduct]
  | append_singleton hs h ih =>
      rw [List.length_append, List.length_singleton,
        iteratedRealDifference_append_singleton, forwardDifference_pow_eq]
      rw [iteratedRealDifference_finsetSum, sum_range_succ]
      have hzero :
          (∑ i ∈ range hs.length,
            iteratedRealDifference
              (fun x : Int =>
                ((((hs.length + 1).choose i : Nat) : Real) *
                  (h : Real) ^ (hs.length + 1 - i)) * (x : Real) ^ i)
              hs x) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [iteratedRealDifference_smul]
        rw [iteratedRealDifference_pow_eq_zero_of_lt hs (mem_range.mp hi), mul_zero]
      rw [hzero, zero_add, iteratedRealDifference_smul, ih]
      simp only [Nat.choose_succ_self_right, Nat.cast_succ,
        Nat.add_sub_cancel_left, pow_one, Nat.factorial_succ]
      rw [realShiftProduct_append_singleton]
      push_cast
      ring

private lemma iteratedRealDifference_scaled_full (alpha : Real) (hs : List Int)
    (x : Int) :
    iteratedRealDifference (fun z => alpha * (z : Real) ^ hs.length) hs x =
      alpha * (Nat.factorial hs.length : Real) * realShiftProduct hs := by
  rw [iteratedRealDifference_smul, iteratedRealDifference_pow_length]
  ring

private lemma iteratedMonomialDifference_sub {alpha : Real} {k : Nat}
    {hs : List Int} (hk : 1 ≤ k) (hhs : hs.length = k - 1) (x y : Int) :
    iteratedRealDifference (fun z => alpha * (z : Real) ^ k) hs x -
        iteratedRealDifference (fun z => alpha * (z : Real) ^ k) hs y =
      alpha * (Nat.factorial k : Real) * realShiftProduct hs *
        ((x - y : Int) : Real) := by
  have hlen : ((x - y) :: hs).length = k := by
    rw [List.length_cons, hhs]
    exact Nat.sub_add_cancel hk
  have hfull := iteratedRealDifference_scaled_full alpha ((x - y) :: hs) y
  rw [hlen] at hfull
  simp only [iteratedRealDifference, realShiftProduct] at hfull
  have hyx : y + (x - y) = x := by omega
  rw [hyx] at hfull
  change
    iteratedRealDifference (fun z => alpha * (z : Real) ^ k) hs x -
        iteratedRealDifference (fun z => alpha * (z : Real) ^ k) hs y =
      alpha * (Nat.factorial k : Real) *
        (((x - y : Int) : Real) * realShiftProduct hs) at hfull
  calc
    _ = alpha * (Nat.factorial k : Real) *
        (((x - y : Int) : Real) * realShiftProduct hs) := hfull
    _ = _ := by ring

private lemma differenceBounds_card_le (t : Nat) (hs : List Int) :
    (Icc (differenceBounds 1 t hs).1 (differenceBounds 1 t hs).2).card ≤ t := by
  simpa using card_le_card (differenceBounds_interval_subset 1 t hs)

private lemma finiteDifferenceSum_monomial_le {alpha : Real} {k t : Nat}
    {hs : List Int} (hk : 1 ≤ k) (hhs : hs.length = k - 1) :
    ‖finiteDifferenceSum (fun z => alpha * (z : Real) ^ k) 1 t hs‖ ≤
      geometricSumMajorant t
        (alpha * (Nat.factorial k : Real) *
          realShiftProduct hs) := by
  set b := differenceBounds 1 t hs
  have hsum : finiteDifferenceSum (fun z => alpha * (z : Real) ^ k) 1 t hs =
      ∑ x ∈ Icc b.1 b.2, realExponential (alpha * (Nat.factorial k : Real) *
        realShiftProduct hs * x + (iteratedRealDifference (fun z => alpha * (z : Real) ^ k)
          hs b.1 - alpha * (Nat.factorial k : Real) * realShiftProduct hs * b.1)) := by
    refine Finset.sum_congr rfl fun x _ => congrArg realExponential ?_
    have := iteratedMonomialDifference_sub (alpha := alpha) hk hhs x b.1
    push_cast at this
    linarith
  rw [hsum]
  exact (norm_sum_linear_phase_Icc_le _ _ _ _).trans
    (geometricSumMajorant_mono (differenceBounds_card_le t hs) _)

/-! ## Removing zero shifts and signs

Zero shifts are kept separate: they are precisely the source of the
`t⁻¹` term in Weyl's inequality.  Every nonzero signed shift has a positive
absolute value in `(0,t)`, with fibres of size at most two.
-/

private lemma finiteDifferenceSum_norm_le (phi : Int → Real) (t : Nat)
    (hs : List Int) : ‖finiteDifferenceSum phi 1 t hs‖ ≤ t :=
  (norm_sum_le _ _).trans (by
    simpa [realExponential_norm] using (Nat.cast_le (α := Real)).2 (differenceBounds_card_le t hs))

private lemma iteratedDifferenceNormSum_trivial (phi : Int → Real)
    (t j : Nat) (hs : List Int) :
    iteratedDifferenceNormSum phi t j hs ≤
      ((weylShiftRange t).card : Real) ^ j * t := by
  induction j generalizing hs with
  | zero =>
      simpa [iteratedDifferenceNormSum] using finiteDifferenceSum_norm_le phi t hs
  | succ j ih =>
      simp only [iteratedDifferenceNormSum]
      calc
        (∑ h ∈ weylShiftRange t,
            iteratedDifferenceNormSum phi t j (h :: hs)) ≤
            ∑ _h ∈ weylShiftRange t,
              (((weylShiftRange t).card : Real) ^ j * t) := by
          gcongr with h _
          exact ih (h :: hs)
        _ = ((weylShiftRange t).card : Real) ^ (j + 1) * t := by
          simp [pow_succ]
          ring

private def iteratedNonzeroDifferenceNormSum (phi : Int → Real) (t : Nat) :
    Nat → List Int → Real
  | 0, hs => ‖finiteDifferenceSum phi 1 t hs‖
  | j + 1, hs =>
      ∑ h ∈ (weylShiftRange t).erase 0,
        iteratedNonzeroDifferenceNormSum phi t j (h :: hs)

private def weylZeroContribution (t : Nat) : Nat → Real
  | 0 => 0
  | j + 1 =>
      ((weylShiftRange t).card : Real) ^ j * t +
        (weylShiftRange t).card * weylZeroContribution t j

private lemma weylZeroContribution_nonneg (t j : Nat) :
    0 ≤ weylZeroContribution t j := by
  induction j with
  | zero => simp [weylZeroContribution]
  | succ j ih =>
      simp only [weylZeroContribution]
      exact add_nonneg (by positivity) (mul_nonneg (by positivity) ih)

private lemma iteratedDifferenceNormSum_split_zero (phi : Int → Real)
    {t : Nat} (ht : 1 ≤ t) (j : Nat) (hs : List Int) :
    iteratedDifferenceNormSum phi t j hs ≤
      weylZeroContribution t j +
        iteratedNonzeroDifferenceNormSum phi t j hs := by
  have hzero : (0 : Int) ∈ weylShiftRange t := mem_Ioo.mpr ⟨by omega, by omega⟩
  induction j generalizing hs with
  | zero => simp [iteratedDifferenceNormSum, iteratedNonzeroDifferenceNormSum,
      weylZeroContribution]
  | succ j ih =>
      simp only [iteratedDifferenceNormSum, iteratedNonzeroDifferenceNormSum,
        weylZeroContribution]
      rw [← Finset.sum_erase_add _ _ hzero]
      have hsum := Finset.sum_le_sum fun h (_ : h ∈ (weylShiftRange t).erase 0) => ih (h :: hs)
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
      have hcard : (((weylShiftRange t).erase 0).card : Real) ≤ (weylShiftRange t).card := by
        exact_mod_cast card_erase_le
      linarith [iteratedDifferenceNormSum_trivial phi t j (0 :: hs),
        mul_le_mul_of_nonneg_right hcard (weylZeroContribution_nonneg t j)]

private lemma weylZeroContribution_le (t j : Nat) :
    weylZeroContribution t j ≤
      (j : Real) * t * ((weylShiftRange t).card : Real) ^ (j - 1) := by
  induction j with
  | zero => simp [weylZeroContribution]
  | succ j ih =>
      cases j with
      | zero => simp [weylZeroContribution]
      | succ j =>
          simp only [weylZeroContribution]
          calc
            ((weylShiftRange t).card : Real) ^ (j + 1) * t +
                (weylShiftRange t).card * weylZeroContribution t (j + 1) ≤
              ((weylShiftRange t).card : Real) ^ (j + 1) * t +
                (weylShiftRange t).card *
                  ((j + 1 : Nat) * t *
                    ((weylShiftRange t).card : Real) ^ j) := by
              apply add_le_add
              · rfl
              · apply mul_le_mul_of_nonneg_left _ (by positivity)
                simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using ih
            _ = ((j + 2 : Nat) : Real) * t *
                ((weylShiftRange t).card : Real) ^ (j + 1) := by
              rw [pow_succ]
              push_cast
              ring

private lemma geometricSumMajorant_neg (n : Nat) (x : Real) :
    geometricSumMajorant n (-x) = geometricSumMajorant n x := by
  simp [geometricSumMajorant]

private def natAbsShiftProduct (hs : List Int) : Nat :=
  (hs.map Int.natAbs).prod

private lemma realShiftProduct_eq_cast_prod (hs : List Int) :
    realShiftProduct hs = (hs.prod : Int) := by
  induction hs with
  | nil => simp [realShiftProduct]
  | cons h hs ih =>
      change (h : Real) * realShiftProduct hs = ((h * hs.prod : Int) : Real)
      rw [ih, Int.cast_mul]

private lemma natAbsShiftProduct_eq_natAbs_prod (hs : List Int) :
    natAbsShiftProduct hs = hs.prod.natAbs := by
  induction hs with
  | nil => simp [natAbsShiftProduct]
  | cons h hs ih =>
      change h.natAbs * natAbsShiftProduct hs = (h * hs.prod).natAbs
      rw [Int.natAbs_mul, ih]

private lemma geometricSumMajorant_signedProduct (n : Nat) (c : Real)
    (hs : List Int) :
    geometricSumMajorant n (c * realShiftProduct hs) =
      geometricSumMajorant n (c * natAbsShiftProduct hs) := by
  rw [realShiftProduct_eq_cast_prod, natAbsShiftProduct_eq_natAbs_prod]
  rcases hs.prod.natAbs_eq with hprod | hprod
  · have hprodReal : (hs.prod : Real) = (hs.prod.natAbs : Nat) := by
      have hcast := congrArg (fun z : Int => (z : Real)) hprod
      simpa only [Int.cast_natCast] using hcast
    rw [hprodReal]
  · have hprodReal : (hs.prod : Real) = -(hs.prod.natAbs : Nat) := by
      have hcast := congrArg (fun z : Int => (z : Real)) hprod
      simpa only [Int.cast_neg, Int.cast_natCast] using hcast
    rw [hprodReal]
    convert geometricSumMajorant_neg n
      (c * (hs.prod.natAbs : Nat)) using 1 <;> ring

private lemma sum_weylShiftRange_erase_zero_natAbs_le {t : Nat}
    (f : Nat → Real) (hf : ∀ n, 0 ≤ f n) :
    ∑ h ∈ (weylShiftRange t).erase 0, f h.natAbs ≤
      2 * ∑ n ∈ Icc 1 t, f n := by
  have hmaps : ∀ h ∈ (weylShiftRange t).erase 0, h.natAbs ∈ Icc 1 t := fun h hh => by
    simp only [mem_erase, weylShiftRange, mem_Ioo, mem_Icc] at hh ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hcard : (((weylShiftRange t).erase 0).filter (·.natAbs = n)).card ≤ 2 :=
    (card_le_card (t := {(n : Int), -(n : Int)}) fun h hh => by
      rw [mem_filter] at hh
      rw [mem_insert, mem_singleton]
      omega).trans card_le_two
  calc _ = ∑ _h ∈ ((weylShiftRange t).erase 0).filter (·.natAbs = n), f n :=
        Finset.sum_congr rfl fun h hh => by rw [(mem_filter.mp hh).2]
    _ ≤ 2 * f n := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf n)

private def positiveProductMajorantSum (alpha : Real) (k t : Nat) :
    Nat → Nat → Real
  | 0, n => geometricSumMajorant t
      (alpha * (Nat.factorial k : Real) * n)
  | j + 1, n =>
      ∑ h ∈ Icc 1 t, positiveProductMajorantSum alpha k t j (h * n)

private lemma positiveProductMajorantSum_nonneg (alpha : Real) (k t j n : Nat) :
    0 ≤ positiveProductMajorantSum alpha k t j n := by
  induction j generalizing n with
  | zero => exact geometricSumMajorant_nonneg _ _
  | succ j ih =>
      simp only [positiveProductMajorantSum]
      exact sum_nonneg fun h _ => ih _

private lemma iteratedNonzeroDifferenceNormSum_le_positive
    {alpha : Real} {k t j : Nat} (hk : 1 ≤ k) (hs : List Int)
    (hlen : hs.length + j = k - 1) :
    iteratedNonzeroDifferenceNormSum
        (fun z => alpha * (z : Real) ^ k) t j hs ≤
      (2 : Real) ^ j *
        positiveProductMajorantSum alpha k t j (natAbsShiftProduct hs) := by
  induction j generalizing hs with
  | zero =>
      simp only [iteratedNonzeroDifferenceNormSum, pow_zero, one_mul,
        positiveProductMajorantSum, Nat.add_zero] at hlen ⊢
      refine (finiteDifferenceSum_monomial_le hk hlen).trans_eq ?_
      exact geometricSumMajorant_signedProduct t
        (alpha * (Nat.factorial k : Real)) hs
  | succ j ih =>
      simp only [iteratedNonzeroDifferenceNormSum, positiveProductMajorantSum]
      calc _ ≤ ∑ h ∈ (weylShiftRange t).erase 0, (2 : Real) ^ j *
            positiveProductMajorantSum alpha k t j (h.natAbs * natAbsShiftProduct hs) :=
          Finset.sum_le_sum fun h _ => ih (h :: hs) (by simp only [List.length_cons]; omega)
        _ ≤ _ := by
          rw [← Finset.mul_sum, pow_succ, mul_assoc]
          gcongr
          exact sum_weylShiftRange_erase_zero_natAbs_le
            (fun n => positiveProductMajorantSum alpha k t j (n * natAbsShiftProduct hs))
            fun n => positiveProductMajorantSum_nonneg alpha k t j _

/-! A list model of ordered positive tuples.  It mirrors the recursive sum
above and will let us group tuples by their product without dependent-type
bookkeeping. -/

private def listConsEmbedding (α : Type*) : α × List α ↪ List α where
  toFun p := p.1 :: p.2
  inj' := by
    intro p q hpq
    cases p with
    | mk pHead pTail =>
      cases q with
      | mk qHead qTail =>
        simp only at hpq
        simpa using hpq

private def listsIn {α : Type*} [DecidableEq α] (s : Finset α) :
    Nat → Finset (List α)
  | 0 => {[]}
  | r + 1 => (s ×ˢ listsIn s r).map (listConsEmbedding α)

private lemma mem_listsIn_iff {α : Type*} [DecidableEq α]
    (s : Finset α) (r : Nat) (l : List α) :
    l ∈ listsIn s r ↔ l.length = r ∧ ∀ x ∈ l, x ∈ s := by
  induction r generalizing l with
  | zero => cases l <;> simp [listsIn]
  | succ r ih => cases l <;> simp [listsIn, listConsEmbedding, ih, and_left_comm]

private lemma card_listsIn {α : Type*} [DecidableEq α]
    (s : Finset α) (r : Nat) :
    (listsIn s r).card = s.card ^ r := by
  induction r with
  | zero => simp [listsIn]
  | succ r ih =>
      rw [listsIn, card_map, card_product, ih, pow_succ]
      exact Nat.mul_comm _ _

private lemma positiveProductMajorantSum_eq_sum_lists
    (alpha : Real) (k t j n : Nat) :
    positiveProductMajorantSum alpha k t j n =
      ∑ l ∈ listsIn (Icc 1 t) j,
        geometricSumMajorant t
          (alpha * (Nat.factorial k : Real) * (n * l.prod)) := by
  induction j generalizing n with
  | zero => simp [positiveProductMajorantSum, listsIn]
  | succ j ih =>
      simp only [positiveProductMajorantSum, listsIn, Finset.sum_map, Finset.sum_product, ih,
        listConsEmbedding, Function.Embedding.coeFn_mk, List.prod_cons, Nat.cast_mul]
      exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun l _ => by ring_nf

/-! ## A fully explicit subpower divisor bound

The usual proof of Weyl's inequality hides the number of factorizations of
an integer in `t^epsilon`.  The next estimates make that loss explicit.  The
parameter will later be specialized to `m = 8 * k^3`; the very large
threshold in Lemma 5.3 then absorbs the factor `m^(2^m)`.
-/

private lemma nat_succ_le_mul_two_pow_div (e m : Nat) (hm : 1 ≤ m) :
    e + 1 ≤ m * 2 ^ (e / m) := by
  have hmpos : 0 < m := by omega
  have hmod := Nat.mod_lt e hmpos
  have hdecomp := Nat.mod_add_div e m
  have hquot : e / m + 1 ≤ 2 ^ (e / m) := nat_succ_le_two_pow (e / m)
  calc
    e + 1 ≤ m * (e / m + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ ≤ m * 2 ^ (e / m) := Nat.mul_le_mul_left m hquot

private lemma divisor_factor_power_bound (p e m : Nat)
    (hp : 2 ≤ p) (hm : 1 ≤ m) :
    (e + 1) ^ m ≤
      (if p < 2 ^ m then m ^ m else 1) * p ^ e := by
  by_cases hsmall : p < 2 ^ m
  · rw [if_pos hsmall]
    have hbase := nat_succ_le_mul_two_pow_div e m hm
    calc
      (e + 1) ^ m ≤ (m * 2 ^ (e / m)) ^ m :=
        Nat.pow_le_pow_left hbase m
      _ = m ^ m * 2 ^ ((e / m) * m) := by rw [mul_pow, ← pow_mul]
      _ ≤ m ^ m * 2 ^ e := by
        exact Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self e m))
      _ ≤ m ^ m * p ^ e := by
        exact Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (show 2 ≤ p from hp) e)
  · rw [if_neg hsmall, one_mul]
    have hlarge : 2 ^ m ≤ p := le_of_not_gt hsmall
    calc
      (e + 1) ^ m ≤ (2 ^ e) ^ m :=
        Nat.pow_le_pow_left (nat_succ_le_two_pow e) m
      _ = (2 ^ m) ^ e := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ p ^ e := Nat.pow_le_pow_left hlarge e

private def smallPrimeFactors (n m : Nat) : Finset Nat :=
  n.primeFactors.filter fun p => p < 2 ^ m

private lemma smallPrimeFactors_card_le (n m : Nat) :
    (smallPrimeFactors n m).card ≤ 2 ^ m := by
  calc
    (smallPrimeFactors n m).card ≤ (Finset.range (2 ^ m)).card := by
      apply Finset.card_le_card
      intro p hp
      rw [smallPrimeFactors, Finset.mem_filter] at hp
      exact Finset.mem_range.mpr hp.2
    _ = 2 ^ m := Finset.card_range _

/-- A crude but explicit form of the standard `tau(n) = n^o(1)` estimate.
It is deliberately stated without real powers so the factorization argument
remains entirely in `Nat`. -/
private lemma card_divisors_pow_le (n m : Nat) (hn : n ≠ 0) (hm : 1 ≤ m) :
    n.divisors.card ^ m ≤ m ^ (m * 2 ^ m) * n := by
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ m) ≤
        ∏ p ∈ n.primeFactors,
          ((if p < 2 ^ m then m ^ m else 1) * p ^ n.factorization p) := by
      apply Finset.prod_le_prod
      · intro p _
        exact Nat.zero_le _
      · intro p hp
        apply divisor_factor_power_bound
        · exact (Nat.prime_of_mem_primeFactors hp).two_le
        · exact hm
    _ = (m ^ m) ^ (smallPrimeFactors n m).card * n := by
      have hsmallProd :
          (∏ p ∈ n.primeFactors,
              if p < 2 ^ m then m ^ m else 1) =
            (m ^ m) ^ (smallPrimeFactors n m).card := by
        rw [Finset.prod_ite]
        simp only [Finset.prod_const_one, mul_one, Finset.prod_const,
          smallPrimeFactors]
      rw [Finset.prod_mul_distrib, hsmallProd,
        ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ (m ^ m) ^ (2 ^ m) * n := by
      exact Nat.mul_le_mul_right n
        (Nat.pow_le_pow_right (pow_pos (by omega) _)
          (smallPrimeFactors_card_le n m))
    _ = m ^ (m * 2 ^ m) * n := by rw [pow_mul]

/-!
The preceding integral estimate is used through a real `m`-th root.  Keeping
this intermediate form, rather than immediately simplifying its right-hand
side, makes all zero side conditions explicit and avoids silently appealing
to a real root operation on naturals.
-/

private lemma card_divisors_rpow_le (n m r : Nat) (hn : n ≠ 0) (hm : 1 ≤ m) :
    (n.divisors.card : Real) ^ (r : Real) ≤
      ((m ^ (m * 2 ^ m) * n : Nat) : Real) ^ ((r : Real) / (m : Real)) := by
  have hmpos : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
  have hpowNat := card_divisors_pow_le n m hn hm
  have hpowReal :
      (n.divisors.card : Real) ^ m ≤
        ((m ^ (m * 2 ^ m) * n : Nat) : Real) := by
    exact_mod_cast hpowNat
  have hroot :
      (n.divisors.card : Real) ≤
        ((m ^ (m * 2 ^ m) * n : Nat) : Real) ^ ((m : Real)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos
      (x := (n.divisors.card : Real))
      (y := ((m ^ (m * 2 ^ m) * n : Nat) : Real))
      (z := (m : Real)) (by positivity) (by positivity) hmpos).2
    simpa only [Real.rpow_natCast] using hpowReal
  calc
    (n.divisors.card : Real) ^ (r : Real) ≤
        (((m ^ (m * 2 ^ m) * n : Nat) : Real) ^ ((m : Real)⁻¹)) ^
          (r : Real) := by
      exact Real.rpow_le_rpow (by positivity) hroot (by positivity)
    _ = ((m ^ (m * 2 ^ m) * n : Nat) : Real) ^
          ((r : Real) / (m : Real)) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      rw [div_eq_mul_inv]
      ring

/-! ## Bounded factorizations

After `k - 1` differences, the linear frequency contains a product of
`k - 1` nonzero shifts.  The following finite set records its positive
absolute values.  Bounding every coordinate by a divisor of the product is
slightly less sharp than deleting the final, determined coordinate, but it
has a particularly robust formal proof and is still strong enough for the
repaired `40 * k^3` threshold.
-/

private def boundedFactorizationLists (r n t : Nat) : Finset (List Nat) :=
  (listsIn (Icc 1 t) r).filter fun l => l.prod = n

private lemma boundedFactorizationLists_subset_divisorLists
    (r n t : Nat) (hn : n ≠ 0) :
    boundedFactorizationLists r n t ⊆ listsIn n.divisors r := by
  intro l hl
  rw [boundedFactorizationLists, mem_filter] at hl
  have hshape := (mem_listsIn_iff (Icc 1 t) r l).mp hl.1
  apply (mem_listsIn_iff n.divisors r l).mpr
  refine ⟨hshape.1, ?_⟩
  intro x hx
  apply Nat.mem_divisors.mpr
  refine ⟨?_, hn⟩
  rw [← hl.2]
  exact List.dvd_prod hx

private lemma boundedFactorizationLists_card_le (r n t : Nat) (hn : n ≠ 0) :
    (boundedFactorizationLists r n t).card ≤ n.divisors.card ^ r := by
  calc
    (boundedFactorizationLists r n t).card ≤ (listsIn n.divisors r).card :=
      card_le_card (boundedFactorizationLists_subset_divisorLists r n t hn)
    _ = n.divisors.card ^ r := card_listsIn n.divisors r

private lemma list_prod_le_pow {t : Nat} (l : List Nat)
    (hl : ∀ x ∈ l, x ≤ t) : l.prod ≤ t ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.prod_cons, List.length_cons, pow_succ]
      simpa only [Nat.mul_comm] using
        Nat.mul_le_mul (hl x (by simp))
          (ih fun y hy => hl y (by simp [hy]))

private lemma one_le_list_prod {l : List Nat}
    (hl : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.prod_cons]
      exact one_le_mul (hl x (by simp))
        (ih fun y hy => hl y (by simp [hy]))

private lemma positiveProductMajorantSum_grouped
    (alpha : Real) (k t r : Nat) :
    positiveProductMajorantSum alpha k t r 1 ≤
      ∑ n ∈ Icc 1 (t ^ r),
        (n.divisors.card : Real) ^ r *
          geometricSumMajorant t
            (alpha * (Nat.factorial k : Real) * n) := by
  rw [positiveProductMajorantSum_eq_sum_lists]
  simp_rw [Nat.cast_one, one_mul]
  have hmaps : ∀ l ∈ listsIn (Icc 1 t) r, l.prod ∈ Icc 1 (t ^ r) := by
    intro l hl
    have hshape := (mem_listsIn_iff (Icc 1 t) r l).mp hl
    refine mem_Icc.mpr ⟨one_le_list_prod fun x hx => (mem_Icc.mp (hshape.2 x hx)).1, ?_⟩
    rw [← hshape.1]
    exact list_prod_le_pow _ fun x hx => (mem_Icc.mp (hshape.2 x hx)).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : n ≠ 0 := by
    have := (mem_Icc.mp hn).1
    omega
  calc
    _ = ∑ _l ∈ boundedFactorizationLists r n t,
          geometricSumMajorant t (alpha * (Nat.factorial k : Real) * n) :=
      Finset.sum_congr rfl fun l hl => by rw [(mem_filter.mp hl).2]
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast boundedFactorizationLists_card_le r n t hn0)
        (geometricSumMajorant_nonneg _ _)

/-! ## A rational reciprocal-distance sum

We now prove the elementary estimate customarily used at the end of Weyl
differencing.  The proof is included rather than imported as an asymptotic
`O`-bound.  On a short block the phases are separated; nearest-integer
representatives are put into radial bins.  Each bin has at most two points
(one on either side of zero), and summing the bin bounds is harmonic.
-/

private def nearestIntegerRepresentative (x : Real) : Real := x - round x

private lemma abs_nearestIntegerRepresentative (x : Real) :
    |nearestIntegerRepresentative x| = ‖(x : UnitAddCircle)‖ := by
  simp [nearestIntegerRepresentative, UnitAddCircle.norm_eq]

private lemma abs_nearestIntegerRepresentative_le (x : Real) :
    |nearestIntegerRepresentative x| ≤ 1 / 2 := by
  simpa [nearestIntegerRepresentative] using abs_sub_round x

private def radialBin (Q : Nat) (z : Real) : Nat :=
  ⌊(2 * Q : Real) * |z|⌋₊

private lemma radialBin_le {Q : Nat} {z : Real} (hz : |z| ≤ 1 / 2) :
    radialBin Q z ≤ Q := by
  unfold radialBin
  apply Nat.floor_le_of_le
  norm_num at hz ⊢
  nlinarith

private lemma radialBin_fiber_card_le_two {Q : Nat} (hQ : 1 ≤ Q)
    {I : Type*} [DecidableEq I] (s : Finset I) (z : I → Real)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((2 * Q : Real))⁻¹ ≤ |z i - z j|)
    (m : Nat) :
    (s.filter fun i => radialBin Q (z i) = m).card ≤ 2 := by
  have hQpos : (0 : Real) < 2 * Q := by positivity
  have hbin (x : I) (hx : radialBin Q (z x) = m) :
      (m : Real) ≤ 2 * Q * |z x| ∧ 2 * Q * |z x| < m + 1 :=
    (Nat.floor_eq_iff (by positivity)).mp hx
  -- two points of one bin on the same side of zero would be too close
  refine (card_le_card_of_injOn (fun i => decide (0 ≤ z i)) (fun _ _ => mem_univ _)
    fun i hi j hj hside => ?_).trans (by simp)
  by_contra hij
  obtain ⟨hiS, hi⟩ := mem_filter.mp hi
  obtain ⟨hjS, hj⟩ := mem_filter.mp hj
  obtain ⟨hi1, hi2⟩ := hbin i hi
  obtain ⟨hj1, hj2⟩ := hbin j hj
  have hsame : |z i - z j| = |(|z i| - |z j|)| := by
    simp only [decide_eq_decide] at hside
    rcases le_or_gt 0 (z i) with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (hside.mp h0)]
    · rw [abs_of_neg h0, abs_of_neg (lt_of_not_ge fun h => not_le.mpr h0 (hside.mpr h)),
        neg_sub_neg, abs_sub_comm]
  have hclose : |(2 * Q * |z i| - 2 * Q * |z j|)| < 1 :=
    abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  rw [← mul_sub, abs_mul, abs_of_pos hQpos, ← hsame] at hclose
  have hfar := hsep i hiS j hjS hij
  rw [inv_le_iff_one_le_mul₀ hQpos] at hfar
  linarith

private lemma geometricSumMajorant_le_length (n : Nat) (x : Real) :
    geometricSumMajorant n x ≤ n := by
  unfold geometricSumMajorant
  split_ifs
  · rfl
  · exact min_le_left _ _

private lemma geometricSumMajorant_le_radialBin {Q Y : Nat}
    (x : Real) {m : Nat} (hm : radialBin Q (nearestIntegerRepresentative x) = m)
    (hm0 : m ≠ 0) :
    geometricSumMajorant Y x ≤ (Q : Real) / m := by
  have hmpos : (0 : Real) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm0)
  have hlower : (m : Real) ≤ 2 * Q * |nearestIntegerRepresentative x| := by
    rw [← hm]
    exact Nat.floor_le (by positivity)
  have hrep : 0 < |nearestIntegerRepresentative x| :=
    pos_of_mul_pos_right (hmpos.trans_le hlower) (by positivity)
  rw [abs_nearestIntegerRepresentative] at hlower hrep
  unfold geometricSumMajorant
  rw [if_neg (norm_pos_iff.mp hrep)]
  refine (min_le_right _ _).trans ?_
  rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ hmpos]
  linarith

private lemma separated_geometricSumMajorant_sum_le {Q Y : Nat} (hQ : 1 ≤ Q)
    {I : Type*} [DecidableEq I] (s : Finset I) (phase : I → Real)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((2 * Q : Real))⁻¹ ≤
        |nearestIntegerRepresentative (phase i) -
          nearestIntegerRepresentative (phase j)|) :
    ∑ i ∈ s, geometricSumMajorant Y (phase i) ≤
      2 * Y + 2 * Q * (1 + Real.log Q) := by
  let level : I → Nat := fun i =>
    radialBin Q (nearestIntegerRepresentative (phase i))
  have hmaps : ∀ i ∈ s, level i ∈ range (Q + 1) := fun i _ =>
    mem_range.mpr (Nat.lt_succ_of_le (radialBin_le (abs_nearestIntegerRepresentative_le _)))
  have hcard (m : Nat) : ((s.filter (fun i => level i = m)).card : Real) ≤ 2 := by
    exact_mod_cast radialBin_fiber_card_le_two hQ s
      (fun i => nearestIntegerRepresentative (phase i)) hsep m
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_range_succ']
  have hzero :
      (∑ i ∈ s.filter (fun i => level i = 0), geometricSumMajorant Y (phase i)) ≤ 2 * Y :=
    (sum_le_card_nsmul _ _ _ fun i _ => geometricSumMajorant_le_length Y (phase i)).trans
      (by rw [nsmul_eq_mul]; gcongr; exact hcard 0)
  have hpositive :
      (∑ m ∈ range Q, ∑ i ∈ s.filter (fun i => level i = m + 1),
        geometricSumMajorant Y (phase i)) ≤ 2 * Q * (1 + Real.log Q) := by
    calc
      _ ≤ ∑ m ∈ range Q, 2 * ((Q : Real) / (m + 1 : Nat)) := by
        gcongr with m
        refine (sum_le_card_nsmul _ _ _ fun i hi => geometricSumMajorant_le_radialBin
          (phase i) (mem_filter.mp hi).2 m.succ_ne_zero).trans ?_
        rw [nsmul_eq_mul]
        gcongr
        exact hcard _
      _ = 2 * Q * (harmonic Q : Real) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
      _ ≤ 2 * Q * (1 + Real.log Q) := by
        gcongr
        exact harmonic_le_one_add_log Q
  linarith

private lemma unitAddCircle_intCast_eq_zero (n : Int) :
    ((((n : Int) : Real) : UnitAddCircle)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp [zsmul_eq_mul]⟩

private lemma nearestIntegerRepresentative_mk (x : Real) :
    ((nearestIntegerRepresentative x : Real) : UnitAddCircle) =
      (x : UnitAddCircle) := by
  unfold nearestIntegerRepresentative
  rw [AddCircle.coe_sub, unitAddCircle_intCast_eq_zero, sub_zero]

private lemma rational_circle_norm_lower {a q d : Int}
    (hq : 0 < q) (haq : Int.gcd a q = 1) (hd0 : d ≠ 0)
    (hdq : |d| < q) :
    ((q : Real))⁻¹ ≤
      ‖(((a : Real) * d / q : Real) : UnitAddCircle)‖ := by
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  rw [UnitAddCircle.norm_eq]
  by_contra! hsmall
  set r := round ((a : Real) * d / q)
  -- `|a d - q r| = q |a d / q - r| < 1`, so `q ∣ a d`, hence `q ∣ d`
  have hint : |((a * d - q * r : Int) : Real)| < 1 := by
    rw [show ((a * d - q * r : Int) : Real) = q * ((a : Real) * d / q - r) by
      push_cast
      field_simp, abs_mul, abs_of_pos hqReal]
    calc (q : Real) * |(a : Real) * d / q - r| < q * (q : Real)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hqReal.ne'
  have heq : a * d = q * r := by
    have : |a * d - q * r| < 1 := by exact_mod_cast hint
    rw [abs_lt] at this
    omega
  exact hd0 (Int.eq_zero_of_abs_lt_dvd
    ((Int.isCoprime_iff_gcd_eq_one.mpr haq).symm.dvd_of_dvd_mul_left ⟨r, heq⟩) hdq)

private lemma nearby_rational_phase_separated {a q : Int} {alpha : Real}
    (hq : 0 < q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹)
    {x y : Nat} (hxy : x ≠ y)
    (hshort : |(x : Int) - y| ≤ q / 2) :
    ((2 * q : Real))⁻¹ ≤
      |nearestIntegerRepresentative (alpha * x) -
        nearestIntegerRepresentative (alpha * y)| := by
  set d : Int := (x : Int) - y with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hxy)
  have hrat := rational_circle_norm_lower hq haq hd0 (hshort.trans_lt (by omega))
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  -- the error `e = (alpha - a / q) d` has `|e| ≤ (2 q)⁻¹`
  have herror : |(alpha - (a : Real) / q) * d| ≤ (2 * q : Real)⁻¹ := by
    have htwod : (2 : Real) * |(d : Real)| ≤ q := by exact_mod_cast (by omega : 2 * |d| ≤ q)
    rw [abs_mul]
    calc _ ≤ ((q : Real) ^ 2)⁻¹ * (q / 2) :=
          mul_le_mul halpha (by linarith) (abs_nonneg _) (by positivity)
      _ = (2 * q : Real)⁻¹ := by field_simp
  -- modulo one, `a d / q` is the difference of the representatives minus `e`
  have hcoe : (((a : Real) * d / q : Real) : UnitAddCircle) =
      ((nearestIntegerRepresentative (alpha * x) - nearestIntegerRepresentative (alpha * y) -
        (alpha - (a : Real) / q) * d : Real) : UnitAddCircle) := by
    rw [AddCircle.coe_sub, AddCircle.coe_sub, nearestIntegerRepresentative_mk,
      nearestIntegerRepresentative_mk, ← AddCircle.coe_sub, ← AddCircle.coe_sub]
    congr 1
    rw [hd]
    push_cast
    ring
  rw [hcoe] at hrat
  have hfar := hrat.trans QuotientAddGroup.norm_mk_le_norm
  rw [Real.norm_eq_abs] at hfar
  have hsplit : ((q : Real))⁻¹ = (2 * q : Real)⁻¹ + (2 * q : Real)⁻¹ := by ring
  linarith [abs_sub (nearestIntegerRepresentative (alpha * x) -
    nearestIntegerRepresentative (alpha * y)) ((alpha - (a : Real) / q) * d)]

private def rationalBlock (X L b : Nat) : Finset Nat :=
  (Icc 1 X).filter fun n => n / L = b

private lemma rationalBlock_phase_separated {a q : Int} {alpha : Real}
    (hq : 4 ≤ q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹)
    (X b : Nat) :
    let Q := q.natAbs
    let L := Q / 2
    ∀ x ∈ rationalBlock X L b, ∀ y ∈ rationalBlock X L b,
      x ≠ y →
      ((2 * Q : Real))⁻¹ ≤
        |nearestIntegerRepresentative (alpha * x) -
          nearestIntegerRepresentative (alpha * y)| := by
  dsimp only
  intro x hx y hy hxy
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  rw [rationalBlock, mem_filter] at hx hy
  have hLpos : 0 < q.natAbs / 2 := by omega
  -- `x` and `y` lie in one block of length `|q| / 2`
  have hshort : |(x : Int) - y| ≤ q / 2 := by
    have hxmod := Nat.mod_lt x hLpos
    have hymod := Nat.mod_lt y hLpos
    have hxdec := Nat.mod_add_div x (q.natAbs / 2)
    have hydec := Nat.mod_add_div y (q.natAbs / 2)
    rw [hx.2.trans hy.2.symm] at hxdec
    rw [abs_le]
    omega
  have hQReal : (q.natAbs : Real) = (q : Real) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hqpos)]
  simpa only [hQReal] using
    nearby_rational_phase_separated hqpos haq halpha hxy hshort

private lemma rational_geometric_sum_le (X Y : Nat)
    (hX : 1 ≤ X) (hYX : Y ≤ X)
    (a q : Int) (alpha : Real) (hq : 0 < q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹) :
    ∑ n ∈ Icc 1 X, geometricSumMajorant Y (alpha * n) ≤
      64 * ((X : Real) * Y / q + X + q) *
        (1 + Real.log (2 * X * q)) := by
  lift q to Nat using hq.le with Q
  push_cast
  have hQpos : 1 ≤ Q := by omega
  have hQ : (0 : Real) < Q := by exact_mod_cast hQpos
  have hXr : (1 : Real) ≤ X := by exact_mod_cast hX
  have hXQ : (1 : Real) ≤ 2 * X * Q := by
    have : (1 : Real) ≤ Q := by exact_mod_cast hQpos
    nlinarith
  have hW : 0 ≤ Real.log (2 * X * Q) := Real.log_nonneg hXQ
  by_cases hQsmall : Q < 4
  · -- `q ≤ 3`: the trivial bound `X Y` suffices
    have hsum : ∑ n ∈ Icc 1 X, geometricSumMajorant Y (alpha * n) ≤ (X : Real) * Y :=
      (sum_le_card_nsmul _ _ _ fun n _ => geometricSumMajorant_le_length Y _).trans (by simp)
    have hXY : (X : Real) * Y ≤ 64 * ((X : Real) * Y / Q) := by
      rw [mul_div_assoc', le_div_iff₀ hQ]
      nlinarith [show (0 : Real) ≤ X * Y by positivity,
        show (Q : Real) ≤ 3 by exact_mod_cast (by omega : Q ≤ 3)]
    have : 0 ≤ ((X : Real) * Y / Q + X + Q) * Real.log (2 * X * Q) := by positivity
    linarith [show (0 : Real) ≤ X by positivity]
  -- `q ≥ 4`: blocks of length `q / 2`, each with separated phases
  have hmaps : ∀ n ∈ Icc 1 X, n / (Q / 2) ∈ Icc 0 (X / (Q / 2)) := fun n hn =>
    mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right (mem_Icc.mp hn).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblocks : (((X / (Q / 2) : Nat) + 1 : Nat) : Real) ≤ 3 * X / Q + 1 := by
    have hdiv : ((X / (Q / 2) : Nat) : Real) ≤ X / ((Q / 2 : Nat) : Real) := Nat.cast_div_le
    have hL : (Q : Real) ≤ 3 * ((Q / 2 : Nat) : Real) := by
      exact_mod_cast (by omega : Q ≤ 3 * (Q / 2))
    have : (X : Real) / ((Q / 2 : Nat) : Real) ≤ 3 * X / Q := by
      rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < Q / 2)) hQ]
      linarith [mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg (α := Real) X)]
    push_cast
    linarith
  have hlog : Real.log Q ≤ Real.log (2 * X * Q) := Real.log_le_log hQ (by nlinarith)
  have hYr : (Y : Real) ≤ X := by exact_mod_cast hYX
  calc
    _ ≤ ∑ _b ∈ Icc 0 (X / (Q / 2)), (2 * (Y : Real) + 2 * Q * (1 + Real.log Q)) := by
      gcongr with b
      apply separated_geometricSumMajorant_sum_le hQpos
      simpa only [Int.natAbs_natCast, rationalBlock] using
        rationalBlock_phase_separated (by omega) haq halpha X b
    _ = (((X / (Q / 2) : Nat) + 1 : Nat) : Real) * (2 * Y + 2 * Q * (1 + Real.log Q)) := by
      simp [Nat.card_Icc]
      ring
    _ ≤ (3 * X / Q + 1) * (2 * Y + 2 * Q * (1 + Real.log (2 * X * Q))) := by gcongr
    _ = 6 * (X * Y / Q) + 2 * Y + 6 * X * (1 + Real.log (2 * X * Q)) +
          2 * Q * (1 + Real.log (2 * X * Q)) := by
      field_simp
      ring
    _ ≤ _ := by
      have : 0 ≤ (X : Real) * Y / Q := by positivity
      linarith [mul_nonneg this hW, mul_nonneg (by positivity : (0 : Real) ≤ X) hW,
        mul_nonneg hQ.le hW]

/-! The divisor loss is kept in the exact form delivered by
`card_divisors_rpow_le` until the final threshold calculation. -/

private def divisorMultiplicityLoss (m r t : Nat) : Real :=
  (((m ^ (m * 2 ^ m) * t ^ r : Nat) : Real) ^
    ((r : Real) / (m : Real)))

private lemma divisorMultiplicityLoss_nonneg (m r t : Nat) :
    0 ≤ divisorMultiplicityLoss m r t := by
  unfold divisorMultiplicityLoss
  positivity

private lemma card_divisors_pow_le_divisorMultiplicityLoss
    {n m r t : Nat} (hn : n ≠ 0) (hm : 1 ≤ m) (hnt : n ≤ t ^ r) :
    (n.divisors.card : Real) ^ r ≤ divisorMultiplicityLoss m r t := by
  rw [← Real.rpow_natCast]
  refine (card_divisors_rpow_le n m r hn hm).trans ?_
  unfold divisorMultiplicityLoss
  apply Real.rpow_le_rpow
  · positivity
  · exact_mod_cast Nat.mul_le_mul_left (m ^ (m * 2 ^ m)) hnt
  · positivity

private lemma positiveProductMajorantSum_le_divisorLoss
    (alpha : Real) (k t r m : Nat) (hm : 1 ≤ m) :
    positiveProductMajorantSum alpha k t r 1 ≤
      divisorMultiplicityLoss m r t *
        ∑ n ∈ Icc 1 (t ^ r),
          geometricSumMajorant t
            (alpha * (Nat.factorial k : Real) * n) := by
  refine (positiveProductMajorantSum_grouped alpha k t r).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : n ≠ 0 := by
    have hnOne : 1 ≤ n := (mem_Icc.mp hn).1
    omega
  have hdiv := card_divisors_pow_le_divisorMultiplicityLoss hn0 hm (mem_Icc.mp hn).2
  exact mul_le_mul_of_nonneg_right hdiv (geometricSumMajorant_nonneg _ _)

private def factorialMultiples (k X : Nat) : Finset Nat :=
  (Icc 1 X).image fun n => Nat.factorial k * n

private lemma sum_factorial_frequency_le_full (alpha : Real) (k t X : Nat) :
    ∑ n ∈ Icc 1 X,
        geometricSumMajorant t (alpha * (Nat.factorial k : Real) * n) ≤
      ∑ x ∈ Icc 1 (Nat.factorial k * X),
        geometricSumMajorant t (alpha * x) := by
  have hfac : 0 < Nat.factorial k := Nat.factorial_pos k
  calc
    _ = ∑ x ∈ factorialMultiples k X, geometricSumMajorant t (alpha * x) := by
      rw [factorialMultiples, sum_image]
      · exact Finset.sum_congr rfl fun n _ => by push_cast; ring_nf
      · exact fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hfac hxy
    _ ≤ _ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_)
        fun x _ _ => geometricSumMajorant_nonneg _ _
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
      rw [mem_Icc] at hn ⊢
      exact ⟨one_le_mul hfac hn.1, Nat.mul_le_mul_left _ hn.2⟩

private lemma terminal_positive_sum_rational_bound
    {alpha : Real} {k t r m : Nat} (hm : 1 ≤ m)
    (ht : 1 ≤ t) (hr : 1 ≤ r)
    (a q : Int) (hq : 0 < q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹) :
    positiveProductMajorantSum alpha k t r 1 ≤
      divisorMultiplicityLoss m r t *
        (64 * (((Nat.factorial k * t ^ r : Nat) : Real) * t / q +
            (Nat.factorial k * t ^ r : Nat) + q) *
          (1 + Real.log (2 * (Nat.factorial k * t ^ r : Nat) * q))) := by
  let X := Nat.factorial k * t ^ r
  have hX : 1 ≤ X := by
    exact one_le_mul (Nat.factorial_pos k)
      (one_le_pow₀ ht)
  have htX : t ≤ X := by
    calc
      t = 1 * t := by simp
      _ ≤ Nat.factorial k * t ^ r := by
        exact Nat.mul_le_mul (Nat.factorial_pos k)
          (by simpa only [pow_one] using pow_le_pow_right₀ ht hr)
  refine (positiveProductMajorantSum_le_divisorLoss alpha k t r m hm).trans ?_
  apply mul_le_mul_of_nonneg_left _ (divisorMultiplicityLoss_nonneg m r t)
  refine (sum_factorial_frequency_le_full alpha k t (t ^ r)).trans ?_
  exact rational_geometric_sum_le X t hX htX a q alpha hq haq halpha

/-! ## Quantitative parameters

The paper's claimed `8 k / log log t` overhead is not justified by the cited
proof.  A direct and uniform replacement is obtained by taking the divisor
parameter `m = 8 k^3`.  Since

`(k - 1)^2 / m <= 1 / (8 k)`,

half of the available exponent before the final `2^(k-1)`-st root absorbs
all factorization multiplicities.  The repaired threshold
`2^(2^(40 k^3))` leaves ample room for the remaining explicit constants and
the single logarithm in the rational-sum estimate.
-/

def weylDifferencingPower (k : Nat) : Nat := 2 ^ (k - 1)

private def weylDivisorParameter (k : Nat) : Nat := 8 * k ^ 3

private lemma weyl_divisor_exponent_le {k : Nat} (hk : 1 ≤ k) :
    (((k - 1 : Nat) : Real) ^ 2) / (weylDivisorParameter k : Real) ≤
      (8 * (k : Real))⁻¹ := by
  have hkReal : (1 : Real) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : Real) < k := lt_of_lt_of_le zero_lt_one hkReal
  have hden : (0 : Real) < (weylDivisorParameter k : Nat) := by
    exact_mod_cast (mul_pos (by norm_num : 0 < 8) (pow_pos (by omega : 0 < k) 3))
  unfold weylDivisorParameter at hden ⊢
  rw [div_le_iff₀ hden]
  have hsqNat : (k - 1) ^ 2 ≤ k ^ 2 :=
    Nat.pow_le_pow_left (Nat.sub_le k 1) 2
  have hsq : (((k - 1 : Nat) : Real) ^ 2) ≤ (k : Real) ^ 2 := by
    exact_mod_cast hsqNat
  calc
    (((k - 1 : Nat) : Real) ^ 2) ≤ (k : Real) ^ 2 := hsq
    _ = (8 * (k : Real))⁻¹ *
        ((8 * k ^ 3 : Nat) : Real) := by
      push_cast
      field_simp [ne_of_gt hkPos]

def weylRaisedCoefficientAt (k m : Nat) : Real :=
  let K := weylDifferencingPower k
  (2 : Real) ^ (K + 2 * k + 12) * Nat.factorial k *
    (m : Real) ^ ((k - 1) * 2 ^ m) * (k + 1)

private def weylRaisedCoefficient (k : Nat) : Real :=
  weylRaisedCoefficientAt k (weylDivisorParameter k)

private lemma divisorMultiplicityLoss_eq {m r t : Nat}
    (hm : 1 ≤ m) (ht : 1 ≤ t) :
    divisorMultiplicityLoss m r t =
      (m : Real) ^ (r * 2 ^ m) *
        (t : Real) ^ (((r : Real) ^ 2) / m) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
  have htReal : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  unfold divisorMultiplicityLoss
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  · calc
      (((m : Real) ^ (m * 2 ^ m)) ^ ((r : Real) / m)) =
          (m : Real) ^ (((m * 2 ^ m : Nat) : Real) * ((r : Real) / m)) :=
        (Real.rpow_natCast_mul hmReal.le (m * 2 ^ m) ((r : Real) / m)).symm
      _ = (m : Real) ^ ((r * 2 ^ m : Nat) : Real) := by
        congr 1
        push_cast
        field_simp [ne_of_gt hmReal]
      _ = (m : Real) ^ (r * 2 ^ m) := Real.rpow_natCast _ _
  · calc
      (((t : Real) ^ r) ^ ((r : Real) / m)) =
          (t : Real) ^ ((r : Real) * ((r : Real) / m)) :=
        (Real.rpow_natCast_mul htReal.le r ((r : Real) / m)).symm
      _ = (t : Real) ^ (((r : Real) ^ 2) / m) := by
        congr 1
        ring

private lemma finiteDifferenceSum_nil_eq_weylSum (alpha : Real) (k t : Nat) :
    finiteDifferenceSum (fun z => alpha * (z : Real) ^ k) 1 t [] =
      weylSum alpha k t := by
  simp only [finiteDifferenceSum, differenceBounds, iteratedRealDifference, weylSum]
  refine (Finset.sum_nbij' (fun n : Nat => (n : Int)) Int.toNat (fun n hn => ?_)
    (fun z hz => ?_) (fun n _ => by simp) (fun z hz => ?_) (fun n _ => by simp)).symm
  all_goals (simp only [mem_Icc] at *; omega)

def weylRationalFactor (k t : Nat) (q : Int) : Real :=
  (q : Real)⁻¹ + (t : Real)⁻¹ +
    (q : Real) * (t : Real) ^ (-(k : Real))

private lemma weylRationalFactor_nonneg {k t : Nat} {q : Int}
    (hq : 0 < q) : 0 ≤ weylRationalFactor k t q := by
  unfold weylRationalFactor
  positivity

private lemma inv_le_weylRationalFactor {k t : Nat} {q : Int} (hq : 0 < q) :
    (t : Real)⁻¹ ≤ weylRationalFactor k t q := by
  unfold weylRationalFactor
  have : 0 ≤ (q : Real)⁻¹ + q * (t : Real) ^ (-(k : Real)) := by positivity
  linarith

private lemma pow_mul_weylRationalFactor {k t : Nat} (hk : 1 ≤ k)
    (ht : 1 ≤ t) (q : Int) :
    (t : Real) ^ k * weylRationalFactor k t q =
      (t : Real) ^ k / q + (t : Real) ^ (k - 1) + q := by
  have htReal : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  unfold weylRationalFactor
  rw [mul_add, mul_add]
  have hcancel : (t : Real) ^ k * (t : Real) ^ (-(k : Real)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htReal]
    simp
  have hpred : (t : Real) ^ k * (t : Real)⁻¹ =
      (t : Real) ^ (k - 1) := by
    cases k with
    | zero => omega
    | succ k =>
      change (t : Real) ^ (k + 1) * (t : Real)⁻¹ = (t : Real) ^ k
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ htReal.ne', mul_one]
  rw [hpred, div_eq_mul_inv]
  have hqcancel : (t : Real) ^ k *
      ((q : Real) * (t : Real) ^ (-(k : Real))) = q := by
    calc
      (t : Real) ^ k * ((q : Real) * (t : Real) ^ (-(k : Real))) =
          (q : Real) * ((t : Real) ^ k * (t : Real) ^ (-(k : Real))) := by
        ring
      _ = q := by rw [hcancel, mul_one]
  rw [hqcancel]

private lemma terminal_log_le {k t : Nat} (hk : k ≤ t) (ht : 2 ≤ t)
    {q : Int} (hq : 0 < q) (hqt : q ≤ (t ^ k : Nat)) :
    1 + Real.log
        (2 * (Nat.factorial k * t ^ (k - 1) : Nat) * (q : Real)) ≤
      4 * (k + 1 : Nat) * (1 + Real.log t) := by
  have htReal : (1 : Real) ≤ t := by exact_mod_cast ht.trans' (by norm_num)
  have hqReal : (q : Real) ≤ (t : Real) ^ k := by exact_mod_cast hqt
  -- the argument of the logarithm is at most `t ^ (3 k + 1)`
  have hNat : 2 * (Nat.factorial k * t ^ (k - 1)) ≤ t * (t ^ k * t ^ k) :=
    Nat.mul_le_mul ht (Nat.mul_le_mul ((Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hk k))
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le k 1)))
  have harg : (2 : Real) * (Nat.factorial k * t ^ (k - 1) : Nat) * q ≤ (t : Real) ^ (3 * k + 1) :=
    calc _ ≤ ((t * (t ^ k * t ^ k) : Nat) : Real) * (t : Real) ^ k := by
          gcongr
          exact_mod_cast hNat
      _ = _ := by push_cast; ring
  have hlog := Real.log_le_log (by positivity) harg
  rw [Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith [mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg htReal), Real.log_nonneg htReal]

/-!
This is the quantitative raised form of Weyl's inequality.  All constants
before the final `2^(k-1)`-st root are visible.  The hypotheses `2 ≤ t` and
`k ≤ t` are harmless both for the asymptotic and repaired explicit forms.
-/

theorem weyl_raised_estimate {alpha : Real} {k t m : Nat}
    (hk : 2 ≤ k) (ht : 2 ≤ t) (hkt : k ≤ t) (hm : 1 ≤ m)
    (a q : Int) (hq : 0 < q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹) :
    ‖weylSum alpha k t‖ ^ weylDifferencingPower k ≤
      weylRaisedCoefficientAt k m *
        (t : Real) ^ ((weylDifferencingPower k : Real) +
          (((k - 1 : Nat) : Real) ^ 2) / m) *
        weylRationalFactor k t q * (1 + Real.log t) := by
  have htOne : 1 ≤ t := by omega
  have htReal : (1 : Real) ≤ t := by exact_mod_cast htOne
  have hL : (1 : Real) ≤ 1 + Real.log t := le_add_of_nonneg_right (Real.log_nonneg htReal)
  -- the differencing estimates, stated before their common terms are abbreviated
  have hbase := finiteDifferenceSum_iterated_le (fun z => alpha * (z : Real) ^ k) t (k - 1) []
  rw [finiteDifferenceSum_nil_eq_weylSum] at hbase
  have hsplit := iteratedDifferenceNormSum_split_zero (fun z => alpha * (z : Real) ^ k) htOne
    (k - 1) []
  have hnz := iteratedNonzeroDifferenceNormSum_le_positive (alpha := alpha) (t := t)
    (j := k - 1) (by omega : 1 ≤ k) [] (by simp)
  simp only [natAbsShiftProduct, List.map_nil, List.prod_nil] at hnz
  have hzero := weylZeroContribution_le t (k - 1)
  have hD : ((weylShiftRange t).card : Real) ≤ 2 * t := by
    exact_mod_cast weylShiftRange_card_le t
  have hEk : weylCauchyExponent (k - 1) + k = weylDifferencingPower k := by
    have := nat_succ_le_two_pow (k - 1)
    rw [weylCauchyExponent_eq, weylDifferencingPower]
    omega
  have hterminal := terminal_positive_sum_rational_bound (alpha := alpha) (k := k) (t := t)
    (r := k - 1) (m := m) hm htOne (by omega) a q hq haq halpha
  rw [divisorMultiplicityLoss_eq hm htOne] at hterminal
  have hP0 := positiveProductMajorantSum_nonneg alpha k t (k - 1) 1
  have hB0 := weylRationalFactor_nonneg (k := k) (t := t) hq
  have hBInv := inv_le_weylRationalFactor (k := k) (t := t) hq
  have hbracket : ((Nat.factorial k * t ^ (k - 1) : Nat) : Real) * t / q +
      (Nat.factorial k * t ^ (k - 1) : Nat) + q ≤
        (Nat.factorial k : Real) * ((t : Real) ^ k * weylRationalFactor k t q) := by
    have htk : (t : Real) ^ (k - 1) * t = (t : Real) ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rw [pow_mul_weylRationalFactor (by omega) htOne q]
    push_cast
    rw [mul_assoc _ _ (t : Real), htk, mul_div_assoc]
    linarith [le_mul_of_one_le_left (by positivity : (0 : Real) ≤ q)
      (by exact_mod_cast Nat.factorial_pos k : (1 : Real) ≤ Nat.factorial k)]
  set K := weylDifferencingPower k
  set E := weylCauchyExponent (k - 1)
  set D : Real := ((weylShiftRange t).card : Real)
  set B := weylRationalFactor k t q with hB
  set P := positiveProductMajorantSum alpha k t (k - 1) 1
  set eta : Real := (((k - 1 : Nat) : Real) ^ 2) / m
  set T : Real := (t : Real) ^ ((K : Real) + eta) * B * (1 + Real.log t) with hT
  have heta : 0 ≤ eta := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hT1 : (t : Real) ^ (K - 1) ≤ T := by
    have hpow : (t : Real) ^ (K - 1) ≤ (t : Real) ^ ((K : Real) + eta) * (t : Real)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le htReal
        (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
    rw [hT, mul_assoc]
    exact hpow.trans (mul_le_mul_of_nonneg_left
      (hBInv.trans (le_mul_of_one_le_right hB0 hL)) (by positivity))
  -- the zero shifts: `D ^ E * Z ≤ k (2 t) ^ (K - 1) ≤ k 2 ^ K T`
  have hzeroTerm : D ^ E * weylZeroContribution t (k - 1) ≤ k * (2 ^ K * T) := by
    have hk1 : ((k - 1 : Nat) : Real) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have ht2 : (t : Real) ≤ 2 * t := by linarith
    calc D ^ E * weylZeroContribution t (k - 1)
        ≤ D ^ E * ((k - 1 : Nat) * t * D ^ (k - 1 - 1)) :=
          mul_le_mul_of_nonneg_left hzero (by positivity)
      _ = ((k - 1 : Nat) : Real) * t * D ^ (K - 2) := by
          rw [show K - 2 = E + (k - 1 - 1) by omega, pow_add]
          ring
      _ ≤ k * (2 * t) * (2 * t : Real) ^ (K - 2) := by gcongr
      _ = k * ((2 : Real) ^ (K - 1) * (t : Real) ^ (K - 1)) := by
          rw [← mul_pow, show K - 1 = K - 2 + 1 by omega, pow_succ]
          ring
      _ ≤ k * (2 ^ K * T) := mul_le_mul_of_nonneg_left (mul_le_mul
          (pow_le_pow_right₀ one_le_two (Nat.sub_le K 1)) hT1 (by positivity) (by positivity))
          (Nat.cast_nonneg k)
  -- the constants: `2 ^ K k + 2 ^ (K + 7) k! m ^ … (k + 1) ≤ weylRaisedCoefficientAt k m`
  have hcoef : (2 : Real) ^ K * k +
      2 ^ (K + 7) * Nat.factorial k * (m : Real) ^ ((k - 1) * 2 ^ m) * (k + 1) ≤
        2 ^ (K + 2 * k + 12) * Nat.factorial k * (m : Real) ^ ((k - 1) * 2 ^ m) * (k + 1) := by
    have hc : (k : Real) ≤ Nat.factorial k * (m : Real) ^ ((k - 1) * 2 ^ m) * (k + 1) :=
      (le_add_of_nonneg_right zero_le_one).trans (le_mul_of_one_le_left (by positivity)
        (one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos k)
          (one_le_pow₀ (by exact_mod_cast hm))))
    have h8 : (2 : Real) ^ (K + 7) * 2 ≤ 2 ^ (K + 2 * k + 12) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ one_le_two (by omega)
    linarith [mul_le_mul (pow_le_pow_right₀ one_le_two (by omega : K ≤ K + 7)) hc
      (Nat.cast_nonneg k) (by positivity), mul_le_mul_of_nonneg_right h8
      (by positivity : (0 : Real) ≤ Nat.factorial k * (m : Real) ^ ((k - 1) * 2 ^ m) * (k + 1))]
  by_cases hqt : q ≤ (t ^ k : Nat)
  · -- the main case: the rational-sum estimate for the nonzero shifts
    have hlog := terminal_log_le hkt ht hq hqt
    have hP : P ≤ ((m : Real) ^ ((k - 1) * 2 ^ m) * (t : Real) ^ eta) *
        (64 * ((Nat.factorial k : Real) * ((t : Real) ^ k * B)) *
          (4 * (k + 1 : Nat) * (1 + Real.log t))) :=
      hterminal.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg (by linarith) hlog (by positivity) (by positivity)) (by positivity))
    have hnzTerm : D ^ E * 2 ^ (k - 1) * P ≤
        2 ^ (K + 7) * Nat.factorial k * (m : Real) ^ ((k - 1) * 2 ^ m) * (k + 1) * T := by
      calc D ^ E * 2 ^ (k - 1) * P ≤ (2 * t : Real) ^ E * 2 ^ (k - 1) *
            (((m : Real) ^ ((k - 1) * 2 ^ m) * (t : Real) ^ eta) *
              (64 * ((Nat.factorial k : Real) * ((t : Real) ^ k * B)) *
                (4 * (k + 1 : Nat) * (1 + Real.log t)))) := by gcongr
        _ = _ := by
          rw [hT, Real.rpow_add (by positivity), Real.rpow_natCast,
            show K + 7 = E + (k - 1) + 8 by omega, ← hEk, pow_add, pow_add, pow_add]
          push_cast
          ring
    calc ‖weylSum alpha k t‖ ^ K
        ≤ D ^ E * (weylZeroContribution t (k - 1) + 2 ^ (k - 1) * P) :=
          hbase.trans (mul_le_mul_of_nonneg_left (hsplit.trans (add_le_add le_rfl hnz))
            (by positivity))
      _ ≤ ((2 : Real) ^ K * k +
            2 ^ (K + 7) * Nat.factorial k * (m : Real) ^ ((k - 1) * 2 ^ m) * (k + 1)) * T := by
          linarith
      _ ≤ weylRaisedCoefficientAt k m * T := mul_le_mul_of_nonneg_right hcoef hT0
      _ = _ := by rw [hT]; ring
  · -- for `q > t ^ k` the trivial bound suffices, since then `1 ≤ B`
    have hBOne : 1 ≤ B := by
      have : (1 : Real) < q * (t : Real) ^ (-(k : Real)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
          one_lt_div (by positivity)]
        exact_mod_cast not_le.mp hqt
      have : (0 : Real) ≤ (q : Real)⁻¹ + (t : Real)⁻¹ := by positivity
      rw [hB, weylRationalFactor]
      linarith
    have hA1 : (1 : Real) ≤ weylRaisedCoefficientAt k m := by
      refine le_trans ?_ hcoef
      have : (1 : Real) ≤ 2 ^ K * k := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
        (by exact_mod_cast (by omega : 1 ≤ k))
      have : (0 : Real) ≤ 2 ^ (K + 7) * Nat.factorial k * (m : Real) ^ ((k - 1) * 2 ^ m) *
        (k + 1) := by positivity
      linarith
    calc ‖weylSum alpha k t‖ ^ K ≤ (t : Real) ^ ((K : Real) + eta) :=
          (pow_le_pow_left₀ (norm_nonneg _) (weylSum_norm_le alpha k t) K).trans (by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le htReal (by linarith))
      _ ≤ T := by
          rw [hT, mul_assoc]
          exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hBOne hL)
      _ ≤ weylRaisedCoefficientAt k m * T := le_mul_of_one_le_left hT0 hA1
      _ = _ := by rw [hT]; ring

private lemma weylSum_degree_one_le_geometric (alpha : Real) (t : Nat) :
    ‖weylSum alpha 1 t‖ ≤ geometricSumMajorant t alpha := by
  have hrewrite :
      weylSum alpha 1 t =
        ∑ s ∈ range t, realExponential (alpha * s + alpha) := by
    unfold weylSum
    apply Finset.sum_bij (fun x _ => x - 1)
    · intro x hx
      rw [mem_range]
      have hxIcc := mem_Icc.mp hx
      omega
    · intro x₁ hx₁ x₂ hx₂ heq
      have hx₁Icc := mem_Icc.mp hx₁
      have hx₂Icc := mem_Icc.mp hx₂
      omega
    · intro s hs
      refine ⟨s + 1, ?_, by omega⟩
      rw [mem_Icc]
      exact ⟨by omega, by simpa using mem_range.mp hs⟩
    · intro x hx
      apply congrArg realExponential
      have hxOne : 1 ≤ x := (mem_Icc.mp hx).1
      rw [pow_one, Nat.cast_sub hxOne]
      push_cast
      ring
  rw [hrewrite]
  exact norm_sum_linear_phase_le alpha alpha t

private lemma weyl_degree_one_bound (t : Nat) (a q : Int) (alpha : Real)
    (hq : 0 < q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹) :
    ‖weylSum alpha 1 t‖ ≤ (t : Real) * weylRationalFactor 1 t q := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [weylSum]
  have hfactor : (t : Real) * weylRationalFactor 1 t q =
      (t : Real) / q + 1 + q := by
    simpa only [pow_one, Nat.sub_self, pow_zero] using
      pow_mul_weylRationalFactor (k := 1) (t := t) (by norm_num) ht q
  rw [hfactor]
  refine (weylSum_degree_one_le_geometric alpha t).trans ?_
  by_cases hqOne : q = 1
  · subst q
    exact (geometricSumMajorant_le_length t alpha).trans (by push_cast; linarith)
  -- for `q ≥ 2` the phases `alpha * 1` and `alpha * 0` are separated: `(2 q)⁻¹ ≤ ‖alpha‖`
  have hsep := nearby_rational_phase_separated hq haq halpha (x := 1) (y := 0) one_ne_zero
    (by simp only [Nat.cast_one, Nat.cast_zero, sub_zero, abs_one]; omega)
  rw [show nearestIntegerRepresentative (alpha * (0 : Nat)) = 0 by
    simp [nearestIntegerRepresentative], sub_zero, abs_nearestIntegerRepresentative,
    Nat.cast_one, mul_one, mul_inv] at hsep
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hnorm : (q : Real)⁻¹ ≤ 2 * ‖(alpha : UnitAddCircle)‖ := by linarith
  have hpos : 0 < 2 * ‖(alpha : UnitAddCircle)‖ := (inv_pos.mpr hqReal).trans_le hnorm
  unfold geometricSumMajorant
  rw [if_neg (norm_pos_iff.mp (by linarith : 0 < ‖(alpha : UnitAddCircle)‖))]
  refine (min_le_right _ _).trans (((inv_le_comm₀ hpos hqReal).mpr hnorm).trans ?_)
  linarith [show (0 : Real) ≤ t / q by positivity]

/-- The `K`-th root of a raised bound `S ^ K ≤ A * t ^ (K * e) * B`. -/
private lemma le_of_pow_le_rpow_mul {S A B t e : Real} {K : Nat} (hK : 0 < K) (hS : 0 ≤ S)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hB : 0 ≤ B) (h : S ^ K ≤ A * t ^ ((K : Real) * e) * B) :
    S ≤ A ^ ((K : Real))⁻¹ * t ^ e * B ^ ((K : Real))⁻¹ := by
  have hKpos : (0 : Real) < K := by exact_mod_cast hK
  rw [show t ^ e = (t ^ ((K : Real) * e)) ^ ((K : Real))⁻¹ by
      rw [← Real.rpow_mul ht, mul_right_comm, mul_inv_cancel₀ hKpos.ne', one_mul],
    ← Real.mul_rpow hA (by positivity), ← Real.mul_rpow (by positivity) hB,
    Real.le_rpow_inv_iff_of_pos hS (by positivity) hKpos, Real.rpow_natCast]
  exact h

private theorem weyl_all_epsilon_bound (k : Nat) (hk : 1 ≤ k)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (t : Nat) (a q : Int) (alpha : Real),
        0 < q → Int.gcd a q = 1 →
        |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹ →
        ‖weylSum alpha k t‖ ≤
          C * (t : Real) ^ (1 + epsilon) *
            (weylRationalFactor k t q ^
              ((2 : Real) ^ (k - 1))⁻¹) := by
  by_cases hkOne : k = 1
  · subst k
    refine ⟨1, by norm_num, fun t a q alpha hq haq halpha => ?_⟩
    rw [show ((2 : Real) ^ (1 - 1))⁻¹ = 1 by norm_num, Real.rpow_one, one_mul]
    have hB := weylRationalFactor_nonneg (k := 1) (t := t) hq
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [show weylSum alpha 1 0 = 0 by simp [weylSum], norm_zero]
      exact mul_nonneg (by positivity) hB
    · exact (weyl_degree_one_bound t a q alpha hq haq halpha).trans
        (mul_le_mul_of_nonneg_right
          (Real.self_le_rpow_of_one_le (by exact_mod_cast ht0) (by linarith)) hB)
  have hkTwo : 2 ≤ k := by omega
  set K := weylDifferencingPower k
  have hKNat : 0 < K := pow_pos two_pos _
  have hKpos : (0 : Real) < K := by exact_mod_cast hKNat
  -- `delta` absorbs the logarithm, and `m = m₀ + 1` makes `(k - 1) ^ 2 / m ≤ delta`
  set delta : Real := epsilon * K / 2 with hdelta_def
  have hdelta : 0 < delta := by positivity
  obtain ⟨m₀ : Nat, hm₀⟩ := exists_nat_ge (2 * (((k - 1 : Nat) : Real) ^ 2) / (epsilon * K))
  have heta : (((k - 1 : Nat) : Real) ^ 2) / (m₀ + 1 : Nat) ≤ epsilon * K / 2 := by
    rw [div_le_iff₀ (by positivity)] at hm₀
    rw [div_le_iff₀ (by positivity)]
    push_cast
    linarith [mul_pos hepsilon hKpos]
  have hA0 : 0 ≤ weylRaisedCoefficientAt k (m₀ + 1) := by unfold weylRaisedCoefficientAt; positivity
  set A : Real := weylRaisedCoefficientAt k (m₀ + 1) * (1 + delta⁻¹) with hA_def
  have hA : 0 ≤ A := by positivity
  refine ⟨A ^ ((K : Real))⁻¹ + max 2 k + 1, by positivity,
    fun t a q alpha hq haq halpha => ?_⟩
  rw [show ((2 : Real) ^ (k - 1))⁻¹ = ((K : Real))⁻¹ by simp [K, weylDifferencingPower]]
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [show weylSum alpha k 0 = 0 by simp [weylSum], norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (weylRationalFactor_nonneg hq) _)
  have htOne : (1 : Real) ≤ t := by exact_mod_cast ht0
  have hBinv := inv_le_weylRationalFactor (k := k) (t := t) hq
  have hB : 0 < weylRationalFactor k t q := (inv_pos.mpr (by positivity)).trans_le hBinv
  by_cases htLarge : max 2 k ≤ t
  · -- `‖S‖ ^ K ≤ A t ^ (K (1 + ε)) B`; then take the `K`-th root
    have hraised := weyl_raised_estimate (alpha := alpha) (m := m₀ + 1) hkTwo
      ((le_max_left 2 k).trans htLarge) ((le_max_right 2 k).trans htLarge) (by omega)
      a q hq haq halpha
    have hlog : 1 + Real.log t ≤ (1 + delta⁻¹) * (t : Real) ^ delta := by
      have hlogPow := Real.log_natCast_le_rpow_div t hdelta
      rw [div_eq_mul_inv] at hlogPow
      linarith [Real.one_le_rpow htOne hdelta.le]
    have hraised' : ‖weylSum alpha k t‖ ^ K ≤
        A * (t : Real) ^ (K * (1 + epsilon)) * weylRationalFactor k t q := by
      calc ‖weylSum alpha k t‖ ^ K ≤ weylRaisedCoefficientAt k (m₀ + 1) *
            (t : Real) ^ ((K : Real) + (((k - 1 : Nat) : Real) ^ 2) / (m₀ + 1 : Nat)) *
            weylRationalFactor k t q * ((1 + delta⁻¹) * (t : Real) ^ delta) :=
          hraised.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
        _ = A * (t : Real) ^ ((K : Real) + (((k - 1 : Nat) : Real) ^ 2) / (m₀ + 1 : Nat) +
            delta) * weylRationalFactor k t q := by
          rw [Real.rpow_add (by positivity) _ delta, hA_def]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le htOne (by linarith)) hA) hB.le
    calc ‖weylSum alpha k t‖ ≤ A ^ ((K : Real))⁻¹ * (t : Real) ^ (1 + epsilon) *
          weylRationalFactor k t q ^ ((K : Real))⁻¹ :=
        le_of_pow_le_rpow_mul hKNat (norm_nonneg _) hA (by positivity) hB.le hraised'
      _ ≤ _ := by
        gcongr
        linarith [show (0 : Real) ≤ max 2 k by positivity]
  · -- for small `t`, `‖S‖ ≤ t ≤ C ≤ C t ^ ε` and `t⁻¹ ≤ B ^ (1 / K)`
    have hrootLower : (t : Real)⁻¹ ≤ weylRationalFactor k t q ^ ((K : Real))⁻¹ :=
      (Real.self_le_rpow_of_le_one (by positivity) (inv_le_one_of_one_le₀ htOne)
        (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr hKNat))).trans
        (Real.rpow_le_rpow (by positivity) hBinv (by positivity))
    have htC : (t : Real) ≤ A ^ ((K : Real))⁻¹ + max 2 k + 1 := by
      have : (t : Real) ≤ max 2 k := by exact_mod_cast (by omega : t ≤ max 2 k)
      linarith [Real.rpow_nonneg hA ((K : Real))⁻¹]
    have hpow : 1 ≤ (t : Real) ^ (1 + epsilon) * (t : Real)⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add (by positivity)]
      exact Real.one_le_rpow htOne (by linarith)
    calc ‖weylSum alpha k t‖ ≤ t := weylSum_norm_le alpha k t
      _ ≤ (A ^ ((K : Real))⁻¹ + max 2 k + 1) * ((t : Real) ^ (1 + epsilon) * (t : Real)⁻¹) :=
        htC.trans (le_mul_of_one_le_right (by positivity) hpow)
      _ ≤ _ := by
        rw [← mul_assoc]
        gcongr

/-! ### Absorbing the explicit constants

The estimates below are intentionally very loose.  Their purpose is to
verify, using only elementary power inequalities, that the repaired
double-exponential threshold absorbs every displayed constant.
-/

private def weylRaisedCoefficientNat (k : Nat) : Nat :=
  let K := weylDifferencingPower k
  let m := weylDivisorParameter k
  2 ^ (K + 2 * k + 12) * Nat.factorial k *
    m ^ ((k - 1) * 2 ^ m) * (k + 1)

private lemma weylRaisedCoefficient_eq_natCast (k : Nat) :
    weylRaisedCoefficient k = (weylRaisedCoefficientNat k : Real) := by
  unfold weylRaisedCoefficient weylRaisedCoefficientAt weylRaisedCoefficientNat
  push_cast <;> rfl

lemma nat_le_cube {k : Nat} (hk : 1 ≤ k) : k ≤ k ^ 3 := by
  calc
    k = k * 1 := by simp
    _ ≤ k * k ^ 2 := Nat.mul_le_mul_left k (one_le_pow₀ hk)
    _ = k ^ 3 := by ring

private lemma thirty_two_mul_le_twenty_mul_cube {k : Nat} (hk : 2 ≤ k) :
    32 * k ≤ 20 * k ^ 3 := by
  have hsq : 4 ≤ k ^ 2 := by
    have hpow := Nat.pow_le_pow_left hk 2
    norm_num at hpow
    exact hpow
  calc
    32 * k = 8 * k * 4 := by ring
    _ ≤ 8 * k * k ^ 2 := Nat.mul_le_mul_left (8 * k) hsq
    _ = 8 * k ^ 3 := by ring
    _ ≤ 20 * k ^ 3 := Nat.mul_le_mul_right (k ^ 3) (by norm_num)

private lemma eight_mul_pow_four_le_two_pow_eight_mul_cube {k : Nat}
    (hk : 1 ≤ k) : 8 * k ^ 4 ≤ 2 ^ (8 * k ^ 3) := by
  have hkpow : k ≤ 2 ^ k :=
    (Nat.le_succ k).trans (nat_succ_le_two_pow k)
  have hpow : k ^ 4 ≤ (2 ^ k) ^ 4 := Nat.pow_le_pow_left hkpow 4
  have hkCube : k ≤ k ^ 3 := nat_le_cube hk
  have honeCube : 1 ≤ k ^ 3 := one_le_pow₀ hk
  have hexp : 4 * k + 3 ≤ 8 * k ^ 3 := by
    calc
      4 * k + 3 ≤ 4 * k ^ 3 + 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 4 hkCube) 3
      _ ≤ 4 * k ^ 3 + 4 * k ^ 3 := by omega
      _ = 8 * k ^ 3 := by ring
  calc
    8 * k ^ 4 ≤ 8 * (2 ^ k) ^ 4 := Nat.mul_le_mul_left 8 hpow
    _ = 2 ^ (4 * k + 3) := by
      calc
        8 * (2 ^ k) ^ 4 = 2 ^ 3 * 2 ^ (k * 4) := by
          rw [← pow_mul]
          norm_num
        _ = 2 ^ (3 + k * 4) := by rw [pow_add]
        _ = 2 ^ (4 * k + 3) := by congr 1 <;> omega
    _ ≤ 2 ^ (8 * k ^ 3) := Nat.pow_le_pow_right (by norm_num) hexp

private lemma weylRaisedCoefficientNat_le {k : Nat} (hk : 2 ≤ k) :
    weylRaisedCoefficientNat k ≤ 2 ^ (2 ^ (20 * k ^ 3)) := by
  have hkCube : k ≤ k ^ 3 := nat_le_cube (by omega)
  have hkk : k * k ≤ k ^ 3 := by rw [pow_succ, sq]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hH := nat_succ_le_two_pow (16 * k ^ 3)
  have hK : weylDifferencingPower k ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ k * 32 ≤ 2 ^ (16 * k ^ 3) := by
    rw [show 2 ^ k * 32 = 2 ^ (k + 5) by ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h20 : 2 ^ (16 * k ^ 3) * 4 ≤ 2 ^ (20 * k ^ 3) := by
    rw [show 2 ^ (16 * k ^ 3) * 4 = 2 ^ (16 * k ^ 3 + 2) by ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : 8 * k ^ 3 * ((k - 1) * 2 ^ (8 * k ^ 3)) ≤ 2 ^ (16 * k ^ 3) := by
    have hpoly : 8 * k ^ 3 * (k - 1) ≤ 2 ^ (8 * k ^ 3) := by
      refine le_trans ?_ (eight_mul_pow_four_le_two_pow_eight_mul_cube (by omega : 1 ≤ k))
      rw [show 8 * k ^ 4 = 8 * k ^ 3 * k by ring]
      exact Nat.mul_le_mul_left _ (Nat.sub_le k 1)
    calc
      8 * k ^ 3 * ((k - 1) * 2 ^ (8 * k ^ 3)) = 8 * k ^ 3 * (k - 1) * 2 ^ (8 * k ^ 3) := by ring
      _ ≤ 2 ^ (8 * k ^ 3) * 2 ^ (8 * k ^ 3) := Nat.mul_le_mul_right _ hpoly
      _ = 2 ^ (16 * k ^ 3) := by ring
  -- the four factors are powers of two whose exponents are each at most `2 ^ (16 k³)`
  have hfac : Nat.factorial k ≤ 2 ^ (k * k) := (Nat.factorial_le_pow k).trans (by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((Nat.le_succ k).trans (nat_succ_le_two_pow k)) k)
  have hpow : (8 * k ^ 3) ^ ((k - 1) * 2 ^ (8 * k ^ 3)) ≤
      2 ^ (8 * k ^ 3 * ((k - 1) * 2 ^ (8 * k ^ 3))) := by
    rw [pow_mul 2 (8 * k ^ 3)]
    exact Nat.pow_le_pow_left ((Nat.le_succ _).trans (nat_succ_le_two_pow _)) _
  simp only [weylRaisedCoefficientNat, weylDivisorParameter]
  calc
    _ ≤ 2 ^ (weylDifferencingPower k + 2 * k + 12) * 2 ^ (k * k) *
          2 ^ (8 * k ^ 3 * ((k - 1) * 2 ^ (8 * k ^ 3))) * 2 ^ k :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hfac) hpow) (nat_succ_le_two_pow k)
    _ = 2 ^ (weylDifferencingPower k + 2 * k + 12 + k * k +
          8 * k ^ 3 * ((k - 1) * 2 ^ (8 * k ^ 3)) + k) := by ring
    _ ≤ 2 ^ (2 ^ (20 * k ^ 3)) := Nat.pow_le_pow_right (by norm_num) (by omega)

private lemma thirty_two_mul_le_two_pow {k : Nat} (hk : 2 ≤ k) : 32 * k ≤ 2 ^ (20 * k ^ 3) :=
  (Nat.le_succ _).trans ((nat_succ_le_two_pow (32 * k)).trans
    (Nat.pow_le_pow_right (by norm_num) (thirty_two_mul_le_twenty_mul_cube hk)))

private lemma threshold_root_dominates {k t : Nat} (hk : 2 ≤ k)
    (ht : 2 ^ (2 ^ (40 * k ^ 3)) ≤ t) :
    (2 : Real) ^ (2 ^ (20 * k ^ 3)) ≤
      (t : Real) ^ ((32 * (k : Real))⁻¹) := by
  let G := 2 ^ (20 * k ^ 3)
  let H := 2 ^ (40 * k ^ 3)
  have hkpos : (0 : Real) < k := by positivity
  have hGH : 32 * k * G ≤ H :=
    (Nat.mul_le_mul_right G (thirty_two_mul_le_two_pow hk)).trans
      (le_of_eq (by dsimp only [G, H]; ring))
  have hbase : ((2 ^ H : Nat) : Real) ≤ t := by
    dsimp only [H]
    exact_mod_cast ht
  calc
    (2 : Real) ^ G ≤
        ((2 : Real) ^ H) ^ ((32 * (k : Real))⁻¹) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_natCast_mul (by norm_num : (0 : Real) ≤ 2)]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [mul_comm (H : Real) ((32 * (k : Real))⁻¹), le_inv_mul_iff₀ (mul_pos (by norm_num) hkpos)]
      exact_mod_cast hGH
    _ ≤ (t : Real) ^ ((32 * (k : Real))⁻¹) := by
      apply Real.rpow_le_rpow (by positivity)
      · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbase
      · positivity

private lemma weyl_coefficient_log_absorbed {k t : Nat} (hk : 2 ≤ k)
    (ht : 2 ^ (2 ^ (40 * k ^ 3)) ≤ t) :
    weylRaisedCoefficient k * (1 + Real.log t) ≤
      (1000 : Real) ^ weylDifferencingPower k *
        (t : Real) ^ ((8 * (k : Real))⁻¹) := by
  have htOne : (1 : Real) ≤ t := by exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ 2)).trans ht
  have hR := threshold_root_dominates hk ht
  -- `R = t ^ (1 / (32 k))` dominates `2 ^ (2 ^ (20 k³))`, the coefficient and `1 + 32 k`
  set R : Real := (t : Real) ^ ((32 * (k : Real))⁻¹) with hR_def
  have hcoeff : weylRaisedCoefficient k ≤ R := by
    rw [weylRaisedCoefficient_eq_natCast]
    exact le_trans (by exact_mod_cast weylRaisedCoefficientNat_le hk) hR
  have hlinear : (1 : Real) + 32 * k ≤ R := by
    have h1 := thirty_two_mul_le_two_pow hk
    have h2 := nat_succ_le_two_pow (2 ^ (20 * k ^ 3))
    exact le_trans (by exact_mod_cast (by omega : 1 + 32 * k ≤ 2 ^ 2 ^ (20 * k ^ 3))) hR
  have hlog : 1 + Real.log t ≤ ((1 : Real) + 32 * k) * R := by
    have h := Real.log_natCast_le_rpow_div t (by positivity : (0 : Real) < (32 * (k : Real))⁻¹)
    rw [← hR_def, div_eq_mul_inv, inv_inv] at h
    linarith
  have hRpow : R ^ 3 ≤ (t : Real) ^ ((8 * (k : Real))⁻¹) := by
    rw [hR_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    refine Real.rpow_le_rpow_of_exponent_le htOne ?_
    rw [show (8 * (k : Real))⁻¹ = 4 * (32 * (k : Real))⁻¹ by ring]
    push_cast
    linarith [(by positivity : (0 : Real) ≤ (32 * (k : Real))⁻¹)]
  calc weylRaisedCoefficient k * (1 + Real.log t) ≤ R * (R * R) :=
        mul_le_mul hcoeff (hlog.trans (by gcongr)) (by linarith [Real.log_nonneg htOne])
          (by positivity)
    _ = R ^ 3 := by ring
    _ ≤ (t : Real) ^ ((8 * (k : Real))⁻¹) := hRpow
    _ ≤ _ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))

private def repairedWeylThreshold (k : Nat) : Nat :=
  2 ^ (2 ^ (40 * k ^ 3))

private lemma repairedWeylThreshold_ge_self {k : Nat} (hk : 1 ≤ k) :
    k ≤ repairedWeylThreshold k := by
  unfold repairedWeylThreshold
  refine (Nat.le_succ k).trans (nat_succ_le_two_pow k) |>.trans ?_
  apply Nat.pow_le_pow_right (by norm_num)
  calc
    k ≤ k ^ 3 := nat_le_cube hk
    _ ≤ 40 * k ^ 3 + 1 := by omega
    _ ≤ 2 ^ (40 * k ^ 3) := nat_succ_le_two_pow (40 * k ^ 3)

private theorem weyl_explicit_bound_repaired (k : Nat) (hk : 1 ≤ k)
    (t : Nat) (a q : Int) (alpha : Real)
    (ht : repairedWeylThreshold k ≤ t) (hq : 0 < q)
    (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹) :
    ‖weylSum alpha k t‖ ≤
      1000 * (t : Real) ^
          (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) *
        (weylRationalFactor k t q ^
          ((2 : Real) ^ (k - 1))⁻¹) := by
  have htOne : (1 : Real) ≤ t := by
    exact_mod_cast (one_le_pow₀ (by norm_num) : 1 ≤ repairedWeylThreshold k).trans ht
  have hB := weylRationalFactor_nonneg (k := k) (t := t) hq
  by_cases hkOne : k = 1
  · subst k
    calc
      ‖weylSum alpha 1 t‖ ≤ (t : Real) * weylRationalFactor 1 t q :=
        weyl_degree_one_bound t a q alpha hq haq halpha
      _ ≤ 1000 * (t : Real) ^ (1 + (4 : Real)⁻¹) * weylRationalFactor 1 t q :=
        mul_le_mul_of_nonneg_right ((Real.self_le_rpow_of_one_le htOne (by norm_num)).trans
          (le_mul_of_one_le_left (by positivity) (by norm_num))) hB
      _ = _ := by
        norm_num only [Nat.cast_one, one_mul, one_add_one_eq_two, pow_two,
          Nat.sub_self, pow_zero, inv_one, Real.rpow_one]
  have hkTwo : 2 ≤ k := by omega
  have hkt : k ≤ t := repairedWeylThreshold_ge_self hk |>.trans ht
  have hm : 1 ≤ weylDivisorParameter k := by
    have := nat_le_cube hk
    unfold weylDivisorParameter
    omega
  have hraised := weyl_raised_estimate (alpha := alpha) hkTwo (hkTwo.trans hkt) hkt hm
    a q hq haq halpha
  have habsorb := weyl_coefficient_log_absorbed hkTwo ht
  rw [weylRaisedCoefficient] at habsorb
  have heta := weyl_divisor_exponent_le hk
  have hKform : ((weylDifferencingPower k : Nat) : Real) = (2 : Real) ^ (k - 1) := by
    simp [weylDifferencingPower]
  set K := weylDifferencingPower k
  set eta : Real := (((k - 1 : Nat) : Real) ^ 2) / (weylDivisorParameter k : Nat)
  set B := weylRationalFactor k t q
  have hKpos : (0 : Real) < K := by rw [hKform]; positivity
  -- the bonus exponent `K / (k 2 ^ (k + 1)) = 1 / (4 k)` absorbs `eta + 1 / (8 k)`
  have hexponent : (K : Real) + eta + (8 * (k : Real))⁻¹ ≤
      K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by
    have hkReal : (0 : Real) < k := by positivity
    have hbonus : (K : Real) * ((k : Real) * (2 : Real) ^ (k + 1))⁻¹ = (4 * (k : Real))⁻¹ := by
      rw [hKform, show (2 : Real) ^ (k + 1) = 4 * (2 : Real) ^ (k - 1) by
        rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
        ring]
      field_simp [ne_of_gt hkReal]
    have : (8 * (k : Real))⁻¹ + (8 * (k : Real))⁻¹ = (4 * (k : Real))⁻¹ := by ring
    rw [mul_add, mul_one, hbonus]
    linarith
  have hraised' : ‖weylSum alpha k t‖ ^ K ≤ (1000 : Real) ^ K *
      (t : Real) ^ (K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * B := by
    refine hraised.trans (le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le htOne hexponent) (by positivity)) hB))
    rw [Real.rpow_add (by positivity) ((K : Real) + eta)]
    linarith [mul_le_mul_of_nonneg_right habsorb
      (by positivity : (0 : Real) ≤ (t : Real) ^ ((K : Real) + eta) * B)]
  have hconst : ((1000 : Real) ^ K) ^ ((K : Real))⁻¹ = 1000 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_inv_cancel₀ hKpos.ne',
      Real.rpow_one]
  calc ‖weylSum alpha k t‖ ≤ ((1000 : Real) ^ K) ^ ((K : Real))⁻¹ *
        (t : Real) ^ (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) * B ^ ((K : Real))⁻¹ :=
      le_of_pow_le_rpow_mul (pow_pos two_pos _) (norm_nonneg _) (by positivity) (by positivity)
        hB hraised'
    _ = _ := by rw [hconst, hKform]

/-- Lemma 5.3, including its explicit constant at the proof-supported
`2^(2^(40 k^3))` threshold. -/
theorem lemma_5_3_holds : lemma_5_3 := by
  unfold lemma_5_3
  intro k hk
  constructor
  · intro epsilon hepsilon
    simpa only [weylRationalFactor] using
      weyl_all_epsilon_bound k hk epsilon hepsilon
  · intro t a q alpha ht hq haq halpha
    have htRepaired : repairedWeylThreshold k ≤ t := by
      simpa only [weylThreshold, repairedWeylThreshold] using ht
    simpa only [weylRationalFactor] using
      weyl_explicit_bound_repaired k hk t a q alpha htRepaired hq haq halpha

end LeanProofs.GowersSzemeredi
