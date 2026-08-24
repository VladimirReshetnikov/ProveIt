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
  classical
  have hfactor :
      (∑ s ∈ range n, realExponential (x * s + c)) =
        realExponential c * ∑ s ∈ range n, (realExponential x) ^ s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [← realExponential_nat_mul]
    push_cast
    rw [realExponential_add]
    ring_nf
  rw [hfactor, norm_mul, realExponential_norm, one_mul]
  unfold geometricSumMajorant
  split_ifs with hx
  · calc
      ‖∑ s ∈ range n, (realExponential x) ^ s‖ ≤
          ∑ s ∈ range n, ‖(realExponential x) ^ s‖ := norm_sum_le _ _
      _ = n := by simp [realExponential_norm]
  · have hnorm : 0 < ‖(x : UnitAddCircle)‖ := norm_pos_iff.mpr hx
    have hphase : realExponential x ≠ 1 := by
      intro h
      have hdenom := realExponential_denominator_lower_bound x
      rw [h, sub_self, norm_zero] at hdenom
      linarith
    apply le_min
    · calc
        ‖∑ s ∈ range n, (realExponential x) ^ s‖ ≤
            ∑ s ∈ range n, ‖(realExponential x) ^ s‖ := norm_sum_le _ _
        _ = n := by simp [realExponential_norm]
    · rw [geom_sum_eq hphase, norm_div]
      have hdenomPos : 0 < ‖realExponential x - 1‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hphase)
      apply (div_le_iff₀ hdenomPos).2
      have hlower := realExponential_denominator_lower_bound x
      have hnumerator : ‖realExponential x ^ n - 1‖ ≤ 2 := by
        calc
          ‖realExponential x ^ n - 1‖ ≤
              ‖realExponential x ^ n‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, realExponential_norm]; norm_num
      have htwoNorm : 0 < 2 * ‖(x : UnitAddCircle)‖ := mul_pos (by norm_num) hnorm
      calc
        ‖realExponential x ^ n - 1‖ ≤ 2 := hnumerator
        _ = (2 * ‖(x : UnitAddCircle)‖)⁻¹ *
            (4 * ‖(x : UnitAddCircle)‖) := by
          field_simp [ne_of_gt htwoNorm]
          <;> ring
        _ ≤ (2 * ‖(x : UnitAddCircle)‖)⁻¹ *
            ‖realExponential x - 1‖ := by
          exact mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr htwoNorm.le)

private lemma geometricSumMajorant_mono {m n : Nat} (hmn : m ≤ n) (x : Real) :
    geometricSumMajorant m x ≤ geometricSumMajorant n x := by
  unfold geometricSumMajorant
  split_ifs
  · exact_mod_cast hmn
  · exact min_le_min_right _ (by exact_mod_cast hmn)

private lemma norm_sum_linear_phase_Icc_le (x c : Real) (a b : Int) :
    ‖∑ s ∈ Icc a b, realExponential (x * (s : Real) + c)‖ ≤
      geometricSumMajorant (Icc a b).card x := by
  classical
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  have h := norm_sum_linear_phase_le x (x * (a : Real) + c)
    (b + 1 - a).toNat
  simpa only [Int.card_Icc, Finset.card_map, Finset.card_range,
    Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, Int.cast_natCast,
    Int.cast_add, mul_add, add_assoc, add_left_comm] using h

private lemma weylSum_norm_le (alpha : Real) (k t : Nat) :
    ‖weylSum alpha k t‖ ≤ t := by
  classical
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
  classical
  symm
  unfold finiteCorrelation
  apply Finset.sum_bij (fun x _ => (x + h, x))
  · intro x hx
    obtain ⟨hxS, hxhS⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hxhS, hxS⟩, by omega⟩
  · intro x₁ hx₁ x₂ hx₂ heq
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
  · intro x hx
    rfl

private lemma sum_mul_star_sum_eq_sum_correlation
    (s d : Finset Int) (f : Int → Complex)
    (hd : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ d) :
    (∑ x ∈ s, f x) * star (∑ y ∈ s, f y) =
      ∑ h ∈ d, finiteCorrelation s f h := by
  classical
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
      apply Finset.sum_congr rfl
      intro h _
      exact sum_difference_fiber_eq_correlation s f h

private lemma norm_sum_sq_le_sum_norm_correlation
    (s d : Finset Int) (f : Int → Complex)
    (hd : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ d) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ ∑ h ∈ d, ‖finiteCorrelation s f h‖ := by
  let S : Complex := ∑ x ∈ s, f x
  have hcorr := sum_mul_star_sum_eq_sum_correlation s d f hd
  change ‖S‖ ^ 2 ≤ _
  calc
    ‖S‖ ^ 2 = ‖S * star S‖ := by simp [norm_mul, pow_two]
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
  classical
  unfold finiteCorrelation
  rw [filter_interval_add_mem]
  apply Finset.sum_congr rfl
  intro x _
  rw [star_realExponential, ← realExponential_add]
  congr 1 <;> ring

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
  have hsSubset : s ⊆ Icc (1 : Int) t := by
    exact differenceBounds_interval_subset 1 t hs
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

private lemma iteratedDifferenceNormSum_nonneg (phi : Int → Real) (t j : Nat)
    (hs : List Int) : 0 ≤ iteratedDifferenceNormSum phi t j hs := by
  induction j generalizing hs with
  | zero => simp [iteratedDifferenceNormSum]
  | succ j ih =>
      simp only [iteratedDifferenceNormSum]
      exact sum_nonneg fun h _ => ih _

private lemma iteratedDifferenceNormSqSum_nonneg (phi : Int → Real) (t j : Nat)
    (hs : List Int) : 0 ≤ iteratedDifferenceNormSqSum phi t j hs := by
  induction j generalizing hs with
  | zero => simp [iteratedDifferenceNormSqSum]
  | succ j ih =>
      simp only [iteratedDifferenceNormSqSum]
      exact sum_nonneg fun h _ => ih _

private lemma iteratedDifferenceNormSum_sq_le (phi : Int → Real) (t j : Nat)
    (hs : List Int) :
    iteratedDifferenceNormSum phi t j hs ^ 2 ≤
      (weylShiftRange t).card ^ j *
        iteratedDifferenceNormSqSum phi t j hs := by
  induction j generalizing hs with
  | zero => simp [iteratedDifferenceNormSum, iteratedDifferenceNormSqSum]
  | succ j ih =>
      simp only [iteratedDifferenceNormSum, iteratedDifferenceNormSqSum]
      calc
        (∑ h ∈ weylShiftRange t,
            iteratedDifferenceNormSum phi t j (h :: hs)) ^ 2 ≤
            (weylShiftRange t).card *
              ∑ h ∈ weylShiftRange t,
                iteratedDifferenceNormSum phi t j (h :: hs) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        _ ≤ (weylShiftRange t).card *
              ∑ h ∈ weylShiftRange t,
                ((weylShiftRange t).card ^ j *
                  iteratedDifferenceNormSqSum phi t j (h :: hs)) := by
          gcongr with h hh
          exact ih (h :: hs)
        _ = (weylShiftRange t).card ^ (j + 1) *
              ∑ h ∈ weylShiftRange t,
                iteratedDifferenceNormSqSum phi t j (h :: hs) := by
          calc
            ((weylShiftRange t).card : Real) *
                ∑ h ∈ weylShiftRange t,
                  ((weylShiftRange t).card : Real) ^ j *
                    iteratedDifferenceNormSqSum phi t j (h :: hs) =
              ((weylShiftRange t).card : Real) *
                (((weylShiftRange t).card : Real) ^ j *
                  ∑ h ∈ weylShiftRange t,
                    iteratedDifferenceNormSqSum phi t j (h :: hs)) := by
              congr 1
              rw [Finset.mul_sum]
            _ = _ := by rw [pow_succ]; ring

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
      gcongr with h hh
      exact ih (h :: hs)

/-- The exponent of the ambient shift-range cardinality after `j` exact
Cauchy--Schwarz steps.  Its closed form is `2^j - j - 1`. -/
private def weylCauchyExponent : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * weylCauchyExponent j + j

private lemma nat_succ_le_two_pow (e : Nat) : e + 1 ≤ 2 ^ e := by
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
      have hnonneg :
          0 ≤ (weylShiftRange t).card ^ weylCauchyExponent j *
            iteratedDifferenceNormSum phi t j hs := by
        exact mul_nonneg (by positivity)
          (iteratedDifferenceNormSum_nonneg phi t j hs)
      calc
        ‖finiteDifferenceSum phi 1 t hs‖ ^ (2 ^ (j + 1)) =
            (‖finiteDifferenceSum phi 1 t hs‖ ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
        _ ≤ ((weylShiftRange t).card ^ weylCauchyExponent j *
              iteratedDifferenceNormSum phi t j hs) ^ 2 := by
          exact pow_le_pow_left₀ (by positivity) (ih hs) 2
        _ = (weylShiftRange t).card ^ (2 * weylCauchyExponent j) *
              iteratedDifferenceNormSum phi t j hs ^ 2 := by ring
        _ ≤ (weylShiftRange t).card ^ (2 * weylCauchyExponent j) *
              ((weylShiftRange t).card ^ j *
                iteratedDifferenceNormSqSum phi t j hs) := by
          gcongr
          exact iteratedDifferenceNormSum_sq_le phi t j hs
        _ ≤ (weylShiftRange t).card ^ (2 * weylCauchyExponent j) *
              ((weylShiftRange t).card ^ j *
                iteratedDifferenceNormSum phi t (j + 1) hs) := by
          gcongr
          exact iteratedDifferenceNormSqSum_le_succ phi t j hs
        _ = (weylShiftRange t).card ^ weylCauchyExponent (j + 1) *
              iteratedDifferenceNormSum phi t (j + 1) hs := by
          simp only [weylCauchyExponent, pow_add]
          ring

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
  apply Finset.sum_congr rfl
  intro i hi
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
      simp only [Nat.choose_succ_self_right, Nat.cast_succ, Nat.cast_ofNat,
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
  simp only [iteratedRealDifference, realShiftProduct, List.map_cons,
    List.prod_cons] at hfull
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

private lemma finiteDifferenceSum_monomial_le {alpha : Real} {k t : Nat}
    {hs : List Int} (hk : 1 ≤ k) (hhs : hs.length = k - 1) :
    ‖finiteDifferenceSum (fun z => alpha * (z : Real) ^ k) 1 t hs‖ ≤
      geometricSumMajorant t
        (alpha * (Nat.factorial k : Real) *
          realShiftProduct hs) := by
  let bounds := differenceBounds 1 t hs
  let slope : Real := alpha * (Nat.factorial k : Real) *
    realShiftProduct hs
  let c : Real :=
    iteratedRealDifference (fun z => alpha * (z : Real) ^ k) hs bounds.1 -
      slope * (bounds.1 : Real)
  have hphase : ∀ x : Int,
      iteratedRealDifference (fun z => alpha * (z : Real) ^ k) hs x =
        slope * (x : Real) + c := by
    intro x
    have hsub := iteratedMonomialDifference_sub
      (alpha := alpha) (k := k) (hs := hs) hk hhs x bounds.1
    dsimp only [slope, c]
    push_cast at hsub ⊢
    linarith
  have hcard :
      (Icc bounds.1 bounds.2).card ≤ t := by
    calc
      (Icc bounds.1 bounds.2).card ≤ (Icc (1 : Int) t).card :=
        card_le_card (differenceBounds_interval_subset 1 t hs)
      _ = t := by simp [Int.card_Icc]
  unfold finiteDifferenceSum
  dsimp only [bounds]
  have hrewrite :
      (∑ x ∈ Icc bounds.1 bounds.2,
          realExponential
            (iteratedRealDifference (fun z => alpha * (z : Real) ^ k) hs x)) =
        ∑ x ∈ Icc bounds.1 bounds.2,
          realExponential (slope * (x : Real) + c) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hphase]
  rw [hrewrite]
  exact (norm_sum_linear_phase_Icc_le slope c bounds.1 bounds.2).trans
    (geometricSumMajorant_mono hcard slope)

/-! ## Removing zero shifts and signs

Zero shifts are kept separate: they are precisely the source of the
`t⁻¹` term in Weyl's inequality.  Every nonzero signed shift has a positive
absolute value in `(0,t)`, with fibres of size at most two.
-/

private lemma finiteDifferenceSum_norm_le (phi : Int → Real) (t : Nat)
    (hs : List Int) : ‖finiteDifferenceSum phi 1 t hs‖ ≤ t := by
  classical
  let bounds := differenceBounds 1 t hs
  have hcard : (Icc bounds.1 bounds.2).card ≤ t := by
    calc
      (Icc bounds.1 bounds.2).card ≤ (Icc (1 : Int) t).card :=
        card_le_card (differenceBounds_interval_subset 1 t hs)
      _ = t := by simp [Int.card_Icc]
  unfold finiteDifferenceSum
  dsimp only [bounds]
  calc
    ‖∑ x ∈ Icc bounds.1 bounds.2,
        realExponential (iteratedRealDifference phi hs x)‖ ≤
        ∑ x ∈ Icc bounds.1 bounds.2,
          ‖realExponential (iteratedRealDifference phi hs x)‖ := norm_sum_le _ _
    _ = (Icc bounds.1 bounds.2).card := by simp [realExponential_norm]
    _ ≤ t := by exact_mod_cast hcard

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
          gcongr with h hh
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

private lemma iteratedNonzeroDifferenceNormSum_nonneg
    (phi : Int → Real) (t j : Nat) (hs : List Int) :
    0 ≤ iteratedNonzeroDifferenceNormSum phi t j hs := by
  induction j generalizing hs with
  | zero => simp [iteratedNonzeroDifferenceNormSum]
  | succ j ih =>
      simp only [iteratedNonzeroDifferenceNormSum]
      exact sum_nonneg fun h _ => ih _

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
  have hzero : (0 : Int) ∈ weylShiftRange t := by
    rw [weylShiftRange, mem_Ioo]
    omega
  induction j generalizing hs with
  | zero => simp [iteratedDifferenceNormSum, iteratedNonzeroDifferenceNormSum,
      weylZeroContribution]
  | succ j ih =>
      simp only [iteratedDifferenceNormSum, iteratedNonzeroDifferenceNormSum,
        weylZeroContribution]
      rw [← Finset.sum_erase_add (weylShiftRange t)
        (fun h => iteratedDifferenceNormSum phi t j (h :: hs)) hzero,
        add_comm]
      calc
        iteratedDifferenceNormSum phi t j (0 :: hs) +
            ∑ h ∈ (weylShiftRange t).erase 0,
              iteratedDifferenceNormSum phi t j (h :: hs) ≤
            (((weylShiftRange t).card : Real) ^ j * t) +
              ∑ h ∈ (weylShiftRange t).erase 0,
                (weylZeroContribution t j +
                  iteratedNonzeroDifferenceNormSum phi t j (h :: hs)) := by
          apply add_le_add
          · exact iteratedDifferenceNormSum_trivial phi t j (0 :: hs)
          · apply Finset.sum_le_sum
            intro h hh
            exact ih (h :: hs)
        _ ≤ ((weylShiftRange t).card : Real) ^ j * t +
              (weylShiftRange t).card * weylZeroContribution t j +
              ∑ h ∈ (weylShiftRange t).erase 0,
                iteratedNonzeroDifferenceNormSum phi t j (h :: hs) := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((weylShiftRange t).erase 0).card ≤
              (weylShiftRange t).card := card_erase_le
          have hz : 0 ≤ weylZeroContribution t j :=
            weylZeroContribution_nonneg t j
          have hcardReal : (((weylShiftRange t).erase 0).card : Real) ≤
              (weylShiftRange t).card := by exact_mod_cast hcard
          nlinarith
        _ = _ := by ring

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
  classical
  let s := (weylShiftRange t).erase 0
  let u := Icc 1 t
  have hmaps : ∀ h ∈ s, h.natAbs ∈ u := by
    intro h hh
    dsimp only [s] at hh
    rw [mem_erase, weylShiftRange, mem_Ioo] at hh
    dsimp only [u]
    rw [mem_Icc]
    rcases h.natAbs_eq with habs | habs <;> omega
  rw [show (∑ h ∈ s, f h.natAbs) =
      ∑ n ∈ u, ∑ h ∈ s.filter (fun h => h.natAbs = n), f h.natAbs by
        exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm]
  calc
    (∑ n ∈ u, ∑ h ∈ s.filter (fun h => h.natAbs = n), f h.natAbs) ≤
        ∑ n ∈ u, 2 * f n := by
      gcongr with n hn
      have hsub : s.filter (fun h => h.natAbs = n) ⊆
          ({(n : Int), -(n : Int)} : Finset Int) := by
        intro h hh
        rw [mem_filter] at hh
        rw [mem_insert, mem_singleton]
        rcases h.natAbs_eq with habs | habs
        · left
          omega
        · right
          omega
      have hcard : (s.filter (fun h => h.natAbs = n)).card ≤ 2 := by
        calc
          (s.filter (fun h => h.natAbs = n)).card ≤
              ({(n : Int), -(n : Int)} : Finset Int).card := card_le_card hsub
          _ ≤ 2 := Finset.card_le_two
      rw [show (∑ h ∈ s.filter (fun h => h.natAbs = n), f h.natAbs) =
          (s.filter (fun h => h.natAbs = n)).card * f n by
            calc
              (∑ h ∈ s.filter (fun h => h.natAbs = n), f h.natAbs) =
                  ∑ _h ∈ s.filter (fun h => h.natAbs = n), f n := by
                apply Finset.sum_congr rfl
                intro h hh
                rw [(mem_filter.mp hh).2]
              _ = (s.filter (fun h => h.natAbs = n)).card * f n := by
                simp]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf n)
    _ = 2 * ∑ n ∈ u, f n := by rw [Finset.mul_sum]

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
      calc
        (∑ h ∈ (weylShiftRange t).erase 0,
            iteratedNonzeroDifferenceNormSum
              (fun z => alpha * (z : Real) ^ k) t j (h :: hs)) ≤
            ∑ h ∈ (weylShiftRange t).erase 0,
              ((2 : Real) ^ j *
                positiveProductMajorantSum alpha k t j
                  (h.natAbs * natAbsShiftProduct hs)) := by
          gcongr with h hh
          apply ih (h :: hs)
          simp only [List.length_cons] at hlen ⊢
          omega
        _ = (2 : Real) ^ j *
              ∑ h ∈ (weylShiftRange t).erase 0,
                positiveProductMajorantSum alpha k t j
                  (h.natAbs * natAbsShiftProduct hs) := by
          rw [Finset.mul_sum]
        _ ≤ (2 : Real) ^ j *
              (2 * ∑ h ∈ Icc 1 t,
                positiveProductMajorantSum alpha k t j
                  (h * natAbsShiftProduct hs)) := by
          gcongr
          exact sum_weylShiftRange_erase_zero_natAbs_le
            (t := t)
            (fun n => positiveProductMajorantSum alpha k t j
              (n * natAbsShiftProduct hs))
            (fun n => positiveProductMajorantSum_nonneg alpha k t j _)
        _ = (2 : Real) ^ (j + 1) *
              ∑ h ∈ Icc 1 t,
                positiveProductMajorantSum alpha k t j
                  (h * natAbsShiftProduct hs) := by
          rw [pow_succ]
          ring

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
        simp only [Prod.fst, Prod.snd] at hpq
        simpa using hpq

private def listsIn {α : Type*} [DecidableEq α] (s : Finset α) :
    Nat → Finset (List α)
  | 0 => {[]}
  | r + 1 => (s ×ˢ listsIn s r).map (listConsEmbedding α)

private lemma mem_listsIn_iff {α : Type*} [DecidableEq α]
    (s : Finset α) (r : Nat) (l : List α) :
    l ∈ listsIn s r ↔ l.length = r ∧ ∀ x ∈ l, x ∈ s := by
  induction r generalizing l with
  | zero =>
      constructor
      · intro hl
        have hlNil : l = [] := by simpa [listsIn] using hl
        subst l
        simp
      · rintro ⟨hlen, hall⟩
        have hlNil : l = [] := List.length_eq_zero_iff.mp hlen
        subst l
        simp [listsIn]
  | succ r ih =>
      constructor
      · intro hl
        rw [listsIn, mem_map] at hl
        obtain ⟨p, hp, hpl⟩ := hl
        change p.1 :: p.2 = l at hpl
        subst l
        obtain ⟨hpHead, hpTail⟩ := mem_product.mp hp
        have htail := (ih p.2).mp hpTail
        refine ⟨by simp [htail.1], ?_⟩
        intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hpHead
        · exact htail.2 x hx
      · rintro ⟨hlen, hall⟩
        cases l with
        | nil => simp at hlen
        | cons h l =>
          rw [listsIn, mem_map]
          refine ⟨(h, l), mem_product.mpr ⟨hall h (by simp), ?_⟩, ?_⟩
          · apply (ih l).mpr
            constructor
            · simpa using hlen
            · intro x hx
              exact hall x (by simp [hx])
          · rfl

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
      simp only [positiveProductMajorantSum, listsIn, Finset.sum_map,
        Finset.sum_product]
      simp_rw [ih]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro l hl
      apply congrArg (geometricSumMajorant t)
      have hprod : (listConsEmbedding Nat (h, l)).prod = h * l.prod := by
        rfl
      rw [hprod]
      have hcastHN : ((h * n : Nat) : Real) =
          (h : Real) * (n : Real) := Nat.cast_mul h n
      have hcastProd : ((h * l.prod : Nat) : Real) =
          (h : Real) * (l.prod : Real) := Nat.cast_mul h l.prod
      calc
        alpha * (Nat.factorial k : Real) *
              (((h * n : Nat) : Real) * (l.prod : Real)) =
            alpha * (Nat.factorial k : Real) *
              (((h : Real) * (n : Real)) * (l.prod : Real)) := by
          rw [hcastHN]
        _ = alpha * (Nat.factorial k : Real) *
              ((n : Real) * ((h : Real) * (l.prod : Real))) := by
          ring
        _ = alpha * (Nat.factorial k : Real) *
              ((n : Real) * ((h * l.prod : Nat) : Real)) := by
          rw [hcastProd]

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
    (hp : 2 ≤ p) (he : 1 ≤ e) (hm : 1 ≤ m) :
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
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        apply divisor_factor_power_bound
        · exact (Nat.prime_of_mem_primeFactors hp).two_le
        · apply Nat.one_le_iff_ne_zero.mpr
          exact Finsupp.mem_support_iff.mp (by simpa using hp)
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
  classical
  rw [positiveProductMajorantSum_eq_sum_lists]
  simp_rw [Nat.cast_one, one_mul]
  let s := listsIn (Icc 1 t) r
  let u := Icc 1 (t ^ r)
  have hmaps : ∀ l ∈ s, l.prod ∈ u := by
    intro l hl
    have hshape := (mem_listsIn_iff (Icc 1 t) r l).mp hl
    dsimp only [u]
    rw [mem_Icc]
    constructor
    · apply one_le_list_prod
      intro x hx
      exact (mem_Icc.mp (hshape.2 x hx)).1
    · rw [← hshape.1]
      apply list_prod_le_pow
      intro x hx
      exact (mem_Icc.mp (hshape.2 x hx)).2
  rw [show (∑ l ∈ s,
      geometricSumMajorant t
        (alpha * (Nat.factorial k : Real) * l.prod)) =
      ∑ n ∈ u, ∑ l ∈ s.filter (fun l => l.prod = n),
        geometricSumMajorant t
          (alpha * (Nat.factorial k : Real) * l.prod) by
        exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : n ≠ 0 := by
    have := (mem_Icc.mp hn).1
    omega
  calc
    (∑ l ∈ s.filter (fun l => l.prod = n),
        geometricSumMajorant t
          (alpha * (Nat.factorial k : Real) * l.prod)) =
        (boundedFactorizationLists r n t).card *
          geometricSumMajorant t
            (alpha * (Nat.factorial k : Real) * n) := by
      change (∑ l ∈ boundedFactorizationLists r n t,
        geometricSumMajorant t
          (alpha * (Nat.factorial k : Real) * l.prod)) = _
      simp only [boundedFactorizationLists, mem_filter]
      calc
        (∑ l ∈ boundedFactorizationLists r n t,
            geometricSumMajorant t
              (alpha * (Nat.factorial k : Real) * l.prod)) =
            ∑ _l ∈ boundedFactorizationLists r n t,
              geometricSumMajorant t
                (alpha * (Nat.factorial k : Real) * n) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [(mem_filter.mp hl).2]
        _ = (boundedFactorizationLists r n t).card *
              geometricSumMajorant t
                (alpha * (Nat.factorial k : Real) * n) := by
          simp
    _ ≤ (n.divisors.card : Real) ^ r *
          geometricSumMajorant t
            (alpha * (Nat.factorial k : Real) * n) := by
      have hcardReal :
          ((boundedFactorizationLists r n t).card : Real) ≤
            (n.divisors.card : Real) ^ r := by
        exact_mod_cast boundedFactorizationLists_card_le r n t hn0
      exact mul_le_mul_of_nonneg_right hcardReal
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
  classical
  let fiber := s.filter fun i => radialBin Q (z i) = m
  let side : I → Bool := fun i => decide (0 ≤ z i)
  have hinj : Set.InjOn side (fiber : Set I) := by
    intro i hi j hj hside
    by_contra hij
    have hiS : i ∈ s := (mem_filter.mp hi).1
    have hjS : j ∈ s := (mem_filter.mp hj).1
    have hbins : radialBin Q (z i) = radialBin Q (z j) := by
      rw [(mem_filter.mp hi).2, (mem_filter.mp hj).2]
    have hQpos : (0 : Real) < 2 * Q := by positivity
    have hiLower : (radialBin Q (z i) : Real) ≤ (2 * Q : Real) * |z i| := by
      exact Nat.floor_le (mul_nonneg (by positivity) (abs_nonneg _))
    have hiUpper : (2 * Q : Real) * |z i| < radialBin Q (z i) + 1 := by
      exact Nat.lt_floor_add_one ((2 * Q : Real) * |z i|)
    have hjLower : (radialBin Q (z j) : Real) ≤ (2 * Q : Real) * |z j| := by
      exact Nat.floor_le (mul_nonneg (by positivity) (abs_nonneg _))
    have hjUpper : (2 * Q : Real) * |z j| < radialBin Q (z j) + 1 := by
      exact Nat.lt_floor_add_one ((2 * Q : Real) * |z j|)
    rw [hbins] at hiLower hiUpper
    have hijAbs : |z i| - |z j| < ((2 * Q : Real))⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hQpos, sub_mul]
      linarith
    have hjiAbs : |z j| - |z i| < ((2 * Q : Real))⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hQpos, sub_mul]
      linarith
    have habs : |(|z i| - |z j|)| < ((2 * Q : Real))⁻¹ := by
      rw [abs_lt]
      exact ⟨by linarith, hijAbs⟩
    have hsame : |z i - z j| = |(|z i| - |z j|)| := by
      by_cases hi0 : 0 ≤ z i <;> by_cases hj0 : 0 ≤ z j
      · rw [abs_of_nonneg hi0, abs_of_nonneg hj0]
      · simp [side, hi0, hj0] at hside
      · simp [side, hi0, hj0] at hside
      · have hiNeg : z i < 0 := lt_of_not_ge hi0
        have hjNeg : z j < 0 := lt_of_not_ge hj0
        rw [abs_of_neg hiNeg, abs_of_neg hjNeg, neg_sub_neg, abs_sub_comm]
    have := hsep i hiS j hjS hij
    rw [hsame] at this
    linarith
  calc
    fiber.card = (fiber.image side).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card Bool := Finset.card_le_univ _
    _ = 2 := by decide

private lemma geometricSumMajorant_le_length (n : Nat) (x : Real) :
    geometricSumMajorant n x ≤ n := by
  unfold geometricSumMajorant
  split_ifs
  · rfl
  · exact min_le_left _ _

private lemma geometricSumMajorant_le_radialBin {Q Y : Nat} (hQ : 1 ≤ Q)
    (x : Real) {m : Nat} (hm : radialBin Q (nearestIntegerRepresentative x) = m)
    (hm0 : m ≠ 0) :
    geometricSumMajorant Y x ≤ (Q : Real) / m := by
  have hQpos : (0 : Real) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hmpos : (0 : Real) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm0)
  have hlower : (m : Real) ≤
      (2 * Q : Real) * |nearestIntegerRepresentative x| := by
    rw [← hm]
    exact Nat.floor_le
      (mul_nonneg (by positivity) (abs_nonneg _))
  have hnormpos : 0 < ‖(x : UnitAddCircle)‖ := by
    rw [← abs_nearestIntegerRepresentative]
    by_contra hz
    have : |nearestIntegerRepresentative x| = 0 := le_antisymm
      (not_lt.mp hz) (abs_nonneg _)
    rw [this, mul_zero] at hlower
    linarith
  have hrepPos : 0 < |nearestIntegerRepresentative x| := by
    rwa [abs_nearestIntegerRepresentative]
  have hx0 : (x : UnitAddCircle) ≠ 0 := norm_pos_iff.mp hnormpos
  unfold geometricSumMajorant
  rw [if_neg hx0]
  refine (min_le_right _ _).trans ?_
  rw [← abs_nearestIntegerRepresentative]
  apply (le_div_iff₀ hmpos).2
  calc
    (2 * |nearestIntegerRepresentative x|)⁻¹ * (m : Real) ≤
        (2 * |nearestIntegerRepresentative x|)⁻¹ *
          ((2 * Q : Real) * |nearestIntegerRepresentative x|) := by
      exact mul_le_mul_of_nonneg_left hlower
        (inv_nonneg.mpr (mul_nonneg (by norm_num) (abs_nonneg _)))
    _ = Q := by
      field_simp [ne_of_gt hrepPos]
      <;> ring

private lemma separated_geometricSumMajorant_sum_le {Q Y : Nat} (hQ : 1 ≤ Q)
    {I : Type*} [DecidableEq I] (s : Finset I) (phase : I → Real)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((2 * Q : Real))⁻¹ ≤
        |nearestIntegerRepresentative (phase i) -
          nearestIntegerRepresentative (phase j)|) :
    ∑ i ∈ s, geometricSumMajorant Y (phase i) ≤
      2 * Y + 2 * Q * (1 + Real.log Q) := by
  classical
  let level : I → Nat := fun i =>
    radialBin Q (nearestIntegerRepresentative (phase i))
  let u := Icc 0 Q
  have hmaps : ∀ i ∈ s, level i ∈ u := by
    intro i hi
    dsimp only [u]
    rw [mem_Icc]
    exact ⟨Nat.zero_le _, radialBin_le (abs_nearestIntegerRepresentative_le _)⟩
  rw [show (∑ i ∈ s, geometricSumMajorant Y (phase i)) =
      ∑ m ∈ u, ∑ i ∈ s.filter (fun i => level i = m),
        geometricSumMajorant Y (phase i) by
        exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm]
  rw [← Finset.sum_erase_add u
    (fun m => ∑ i ∈ s.filter (fun i => level i = m),
      geometricSumMajorant Y (phase i))
      (show (0 : Nat) ∈ u by
        dsimp only [u]
        exact mem_Icc.mpr ⟨le_rfl, Nat.zero_le Q⟩), add_comm]
  have hzero :
      (∑ i ∈ s.filter (fun i => level i = 0),
        geometricSumMajorant Y (phase i)) ≤ 2 * Y := by
    calc
      _ ≤ ∑ _i ∈ s.filter (fun i => level i = 0), (Y : Real) := by
        apply Finset.sum_le_sum
        intro i hi
        exact geometricSumMajorant_le_length Y (phase i)
      _ = (s.filter (fun i => level i = 0)).card * Y := by simp
      _ ≤ 2 * Y := by
        have hcard : (s.filter (fun i => level i = 0)).card ≤ 2 :=
          radialBin_fiber_card_le_two hQ s
            (fun i => nearestIntegerRepresentative (phase i)) hsep 0
        have hcardReal :
            ((s.filter (fun i => level i = 0)).card : Real) ≤ 2 := by
          exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hcardReal (by positivity)
  have hpositive :
      (∑ m ∈ u.erase 0,
        ∑ i ∈ s.filter (fun i => level i = m),
          geometricSumMajorant Y (phase i)) ≤
        2 * Q * (1 + Real.log Q) := by
    calc
      _ ≤ ∑ m ∈ u.erase 0, 2 * ((Q : Real) / m) := by
        gcongr with m hm
        calc
          (∑ i ∈ s.filter (fun i => level i = m),
              geometricSumMajorant Y (phase i)) ≤
              ∑ _i ∈ s.filter (fun i => level i = m),
                ((Q : Real) / m) := by
            gcongr with i hi
            apply geometricSumMajorant_le_radialBin hQ
            · exact (mem_filter.mp hi).2
            · exact (mem_erase.mp hm).1
          _ = (s.filter (fun i => level i = m)).card *
                ((Q : Real) / m) := by simp
          _ ≤ 2 * ((Q : Real) / m) := by
            gcongr
            exact_mod_cast radialBin_fiber_card_le_two hQ s
              (fun i => nearestIntegerRepresentative (phase i)) hsep m
      _ ≤ ∑ m ∈ Icc 1 Q, 2 * ((Q : Real) / m) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          dsimp only [u] at hm
          rw [mem_erase, mem_Icc] at hm
          rw [mem_Icc]
          omega
        · intro m hmIcc hmNot
          positivity
      _ = 2 * Q * ∑ m ∈ Icc 1 Q, (m : Real)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 : (m : Real) ≠ 0 := by
          have hmOne : 1 ≤ m := (mem_Icc.mp hm).1
          exact_mod_cast (show m ≠ 0 by omega)
        field_simp [hm0]
        <;> ring
      _ ≤ 2 * Q * (1 + Real.log Q) := by
        gcongr
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast] using harmonic_le_one_add_log Q
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
  by_contra hnot
  have hsmall :
      ‖(((a : Real) * d / q : Real) : UnitAddCircle)‖ < ((q : Real))⁻¹ :=
    lt_of_not_ge hnot
  rw [UnitAddCircle.norm_eq] at hsmall
  let z : Real := (a : Real) * d / q
  let r : Int := round z
  have hrewrite : z - (r : Real) =
      ((a * d - q * r : Int) : Real) / q := by
    dsimp only [z, r]
    push_cast
    field_simp [ne_of_gt hqReal]
    <;> ring
  change |z - (r : Real)| < ((q : Real))⁻¹ at hsmall
  rw [hrewrite, abs_div, abs_of_pos hqReal, inv_eq_one_div,
    div_lt_div_iff_of_pos_right hqReal] at hsmall
  have hint : |a * d - q * r| < (1 : Int) := by
    exact_mod_cast hsmall
  have heq : a * d - q * r = 0 := by
    rw [abs_lt] at hint
    omega
  have hqdvd : q ∣ a * d := by
    refine ⟨r, ?_⟩
    exact sub_eq_zero.mp heq
  have hcop : IsCoprime a q := Int.isCoprime_iff_gcd_eq_one.mpr haq
  have hqd : q ∣ d := hcop.symm.dvd_of_dvd_mul_left hqdvd
  exact hd0 (Int.eq_zero_of_abs_lt_dvd hqd hdq)

private lemma nearby_rational_phase_separated {a q : Int} {alpha : Real}
    (hq : 0 < q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹)
    {x y : Nat} (hxy : x ≠ y)
    (hshort : |(x : Int) - y| ≤ q / 2) :
    ((2 * q : Real))⁻¹ ≤
      |nearestIntegerRepresentative (alpha * x) -
        nearestIntegerRepresentative (alpha * y)| := by
  let d : Int := (x : Int) - y
  have hd0 : d ≠ 0 := by
    intro hd
    apply hxy
    exact_mod_cast sub_eq_zero.mp hd
  have hdq : |d| < q := by
    let Q := q.natAbs
    have hqeq : (Q : Int) = q := by
      dsimp only [Q]
      rw [Int.natCast_natAbs, abs_of_pos hq]
    have hQpos : 0 < Q := Int.natAbs_pos.mpr (ne_of_gt hq)
    have hhalfNat : Q / 2 < Q := Nat.div_lt_self hQpos (by norm_num)
    have hcastDiv : ((Q / 2 : Nat) : Int) = q / 2 := by
      rw [Int.natCast_div, hqeq]
      norm_num
    have : q / 2 < q := by
      calc
        q / 2 = ((Q / 2 : Nat) : Int) := hcastDiv.symm
        _ < (Q : Int) := by exact_mod_cast hhalfNat
        _ = q := hqeq
    exact hshort.trans_lt this
  have hrat := rational_circle_norm_lower hq haq hd0 hdq
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have herror :
      |(alpha - (a : Real) / q) * (d : Real)| ≤ (2 * q : Real)⁻¹ := by
    rw [abs_mul]
    have htwod : 2 * |d| ≤ q := by
      calc
        2 * |d| ≤ 2 * (q / 2) :=
          Int.mul_le_mul_of_nonneg_left hshort (by norm_num)
        _ = (q / 2) * 2 := by ring
        _ ≤ q := Int.ediv_mul_le q (by norm_num)
    have htwodReal : (2 : Real) * |(d : Real)| ≤ q := by
      exact_mod_cast htwod
    calc
      |alpha - (a : Real) / q| * |(d : Real)| ≤
          ((q : Real) ^ 2)⁻¹ * |(d : Real)| := by gcongr
      _ ≤ (2 * q : Real)⁻¹ := by
        rw [inv_mul_eq_div, inv_eq_one_div]
        apply (div_le_div_iff₀ (sq_pos_of_pos hqReal)
          (mul_pos (by norm_num) hqReal)).2
        nlinarith
  have htriangle :
      ‖(((a : Real) * d / q : Real) : UnitAddCircle)‖ ≤
        ‖((alpha * (d : Real) : Real) : UnitAddCircle)‖ +
          |(alpha - (a : Real) / q) * (d : Real)| := by
    have hdecomp :
        (((a : Real) * d / q : Real) : UnitAddCircle) =
          (alpha * (d : Real) : Real) -
            ((alpha - (a : Real) / q) * (d : Real) : Real) := by
      apply congrArg (fun z : Real => (z : UnitAddCircle))
      ring
    rw [hdecomp]
    refine (norm_sub_le _ _).trans ?_
    have herrNorm :
        ‖(((alpha - (a : Real) / q) * (d : Real) : Real) :
            UnitAddCircle)‖ ≤
          ‖((alpha - (a : Real) / q) * (d : Real) : Real)‖ :=
      QuotientAddGroup.norm_mk_le_norm
    simpa only [Real.norm_eq_abs, add_comm] using
      (add_le_add_left herrNorm
        ‖((alpha * (d : Real) : Real) : UnitAddCircle)‖)
  have hcircle : ((2 * q : Real))⁻¹ ≤
      ‖((alpha * (d : Real) : Real) : UnitAddCircle)‖ := by
    have hsplit : ((q : Real))⁻¹ =
        (2 * q : Real)⁻¹ + (2 * q : Real)⁻¹ := by
      field_simp [ne_of_gt hqReal]
      <;> ring
    rw [hsplit] at hrat
    linarith
  have hrep :
      (((alpha * (d : Real) : Real) : UnitAddCircle)) =
        ((nearestIntegerRepresentative (alpha * x) -
          nearestIntegerRepresentative (alpha * y) : Real) : UnitAddCircle) := by
    rw [AddCircle.coe_sub, nearestIntegerRepresentative_mk,
      nearestIntegerRepresentative_mk, ← AddCircle.coe_sub]
    apply congrArg (fun z : Real => (z : UnitAddCircle))
    dsimp only [d]
    push_cast
    ring
  rw [hrep] at hcircle
  refine hcircle.trans ?_
  have hrepNorm :
      ‖((nearestIntegerRepresentative (alpha * x) -
          nearestIntegerRepresentative (alpha * y) : Real) : UnitAddCircle)‖ ≤
        ‖nearestIntegerRepresentative (alpha * x) -
          nearestIntegerRepresentative (alpha * y)‖ :=
    QuotientAddGroup.norm_mk_le_norm
  simpa only [Real.norm_eq_abs] using hrepNorm

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
  have hQ : (q.natAbs : Int) = q := by
    rw [Int.natCast_natAbs, abs_of_pos hqpos]
  rw [rationalBlock, mem_filter] at hx hy
  have hdiv : x / (q.natAbs / 2) = y / (q.natAbs / 2) := hx.2.trans hy.2.symm
  have hLpos : 0 < q.natAbs / 2 := by
    have hfourInt : (4 : Int) ≤ (q.natAbs : Int) := by
      rw [hQ]
      exact hq
    have : 4 ≤ q.natAbs := by exact_mod_cast hfourInt
    omega
  have hshortNat : x.dist y < q.natAbs / 2 := by
    have hxmod := Nat.mod_lt x hLpos
    have hymod := Nat.mod_lt y hLpos
    have hxdec := Nat.mod_add_div x (q.natAbs / 2)
    have hydec := Nat.mod_add_div y (q.natAbs / 2)
    rw [hdiv] at hxdec
    rcases le_total x y with hxyNat | hyxNat
    · rw [Nat.dist_eq_sub_of_le hxyNat]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hyxNat]
      omega
  have hdist : (x.dist y : Int) = |(x : Int) - y| := by
    rcases le_total x y with hxyNat | hyxNat
    · have hxyInt : (x : Int) ≤ (y : Int) := by exact_mod_cast hxyNat
      rw [Nat.dist_eq_sub_of_le hxyNat, Nat.cast_sub hxyNat,
        abs_of_nonpos (sub_nonpos.mpr hxyInt)]
      ring
    · have hyxInt : (y : Int) ≤ (x : Int) := by exact_mod_cast hyxNat
      rw [Nat.dist_eq_sub_of_le_right hyxNat, Nat.cast_sub hyxNat,
        abs_of_nonneg (sub_nonneg.mpr hyxInt)]
  have hhalf : ((q.natAbs / 2 : Nat) : Int) = q / 2 := by
    rw [Int.natCast_div, hQ]
    norm_num
  have hshort : |(x : Int) - y| ≤ q / 2 := by
    have hcast : (x.dist y : Int) ≤ (q.natAbs / 2 : Nat) := by
      exact_mod_cast hshortNat.le
    simpa only [hdist, hhalf] using hcast
  have hQReal : (q.natAbs : Real) = (q : Real) := by
    have hcast := congrArg (fun z : Int => (z : Real)) hQ
    simpa only [Int.cast_natCast] using hcast
  simpa only [hQReal] using
    nearby_rational_phase_separated hqpos haq halpha hxy hshort

private lemma rational_geometric_sum_le (X Y : Nat)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hYX : Y ≤ X)
    (a q : Int) (alpha : Real) (hq : 0 < q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹) :
    ∑ n ∈ Icc 1 X, geometricSumMajorant Y (alpha * n) ≤
      64 * ((X : Real) * Y / q + X + q) *
        (1 + Real.log (2 * X * q)) := by
  classical
  let Q := q.natAbs
  have hQeq : (Q : Int) = q := by
    dsimp only [Q]
    rw [Int.natCast_natAbs, abs_of_pos hq]
  have hQpos : 1 ≤ Q := by
    have hQInt : (1 : Int) ≤ (Q : Int) := by rw [hQeq]; omega
    exact_mod_cast hQInt
  have hsumTrivial :
      (∑ n ∈ Icc 1 X, geometricSumMajorant Y (alpha * n)) ≤
        (X : Real) * Y := by
    calc
      _ ≤ ∑ _n ∈ Icc 1 X, (Y : Real) := by
        gcongr with n hn
        exact geometricSumMajorant_le_length Y (alpha * n)
      _ = (X : Real) * Y := by simp [Nat.card_Icc]
  by_cases hQsmall : Q < 4
  · have hQle : (Q : Real) ≤ 3 := by exact_mod_cast (by omega : Q ≤ 3)
    have hQReal : (0 : Real) < Q := by exact_mod_cast (show 0 < Q by omega)
    have hlog : 1 ≤ 1 + Real.log (2 * (X : Real) * Q) := by
      have harg : (1 : Real) ≤ 2 * X * Q := by
        have hargNat : 1 ≤ 2 * X * Q := by
          have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < (2 : Nat))
            (by omega : 0 < X)) (by omega : 0 < Q)
          omega
        exact_mod_cast hargNat
      have := Real.log_nonneg harg
      linarith
    rw [← hQeq]
    push_cast
    calc
      _ ≤ (X : Real) * Y := hsumTrivial
      _ ≤ 64 * ((X : Real) * Y / Q + X + Q) *
          (1 + Real.log (2 * X * Q)) := by
        have hXY : (0 : Real) < (X : Real) * Y := by positivity
        have hmain : (X : Real) * Y ≤
            64 * ((X : Real) * Y / Q) := by
          have hQ64 : (Q : Real) ≤ 64 := hQle.trans (by norm_num)
          have hone : (1 : Real) ≤ 64 / Q :=
            (le_div_iff₀ hQReal).2 (by simpa using hQ64)
          calc
            (X : Real) * Y ≤ (64 / Q) * ((X : Real) * Y) :=
              le_mul_of_one_le_left hXY.le hone
            _ = 64 * ((X : Real) * Y / Q) := by ring
        calc
          (X : Real) * Y ≤ 64 * ((X : Real) * Y / Q) := hmain
          _ ≤ 64 * ((X : Real) * Y / Q + X + Q) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            nlinarith [show (0 : Real) ≤ X by positivity,
              show (0 : Real) ≤ Q by positivity]
          _ ≤ 64 * ((X : Real) * Y / Q + X + Q) *
              (1 + Real.log (2 * X * Q)) :=
            le_mul_of_one_le_right (by positivity) hlog
  · have hQ4 : 4 ≤ Q := by omega
    have hq4 : (4 : Int) ≤ q := by
      rw [← hQeq]
      exact_mod_cast hQ4
    rw [← hQeq]
    push_cast
    let L := Q / 2
    let blocks := Icc 0 (X / L)
    have hLpos : 0 < L := by dsimp only [L]; omega
    have hmaps : ∀ n ∈ Icc 1 X, n / L ∈ blocks := by
      intro n hn
      dsimp only [blocks]
      rw [mem_Icc]
      exact ⟨Nat.zero_le _, Nat.div_le_div_right (mem_Icc.mp hn).2⟩
    rw [show (∑ n ∈ Icc 1 X, geometricSumMajorant Y (alpha * n)) =
        ∑ b ∈ blocks, ∑ n ∈ rationalBlock X L b,
          geometricSumMajorant Y (alpha * n) by
          exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm]
    have hblock : ∀ b ∈ blocks,
        (∑ n ∈ rationalBlock X L b,
          geometricSumMajorant Y (alpha * n)) ≤
            2 * Y + 2 * Q * (1 + Real.log Q) := by
      intro b hb
      apply separated_geometricSumMajorant_sum_le hQpos
      simpa only [Q, L] using
        rationalBlock_phase_separated hq4 haq halpha X b
    calc
      (∑ b ∈ blocks, ∑ n ∈ rationalBlock X L b,
          geometricSumMajorant Y (alpha * n)) ≤
          ∑ _b ∈ blocks,
            (2 * Y + 2 * Q * (1 + Real.log Q)) := by
        gcongr with b hb
        exact hblock b hb
      _ = ((X / L : Nat) + 1 : Nat) *
          (2 * (Y : Real) + 2 * Q * (1 + Real.log Q)) := by
        simp [blocks, Nat.card_Icc] <;> ring
      _ ≤ 64 * ((X : Real) * Y / Q + X + Q) *
          (1 + Real.log (2 * X * Q)) := by
        have hQReal : (0 : Real) < Q := by positivity
        have hLReal : (0 : Real) < L := by exact_mod_cast hLpos
        have hLlargeNat : Q ≤ 3 * L := by
          dsimp only [L]
          omega
        have hLlarge : (Q : Real) / 3 ≤ L := by
          rw [div_le_iff₀ (by norm_num : (0 : Real) < 3)]
          have hLlargeReal : (Q : Real) ≤ 3 * L := by
            exact_mod_cast hLlargeNat
          simpa only [mul_comm] using hLlargeReal
        have hblockCount : ((X / L : Nat) : Real) + 1 ≤
            3 * (X : Real) / Q + 1 := by
          have hcastDiv : ((X / L : Nat) : Real) ≤ (X : Real) / L :=
            Nat.cast_div_le
          have hdiv : (X : Real) / L ≤ 3 * X / Q := by
            rw [div_le_iff₀ hLReal, div_mul_eq_mul_div,
              le_div_iff₀ hQReal]
            have hQL : (Q : Real) ≤ 3 * L := by nlinarith [hLlarge]
            have hmul := mul_le_mul_of_nonneg_left hQL
              (show (0 : Real) ≤ X by positivity)
            nlinarith [hmul]
          linarith
        have hlogQ : 1 + Real.log Q ≤
            1 + Real.log (2 * (X : Real) * Q) := by
          have hXReal : (1 : Real) ≤ X := by exact_mod_cast hX
          have hQarg : (Q : Real) ≤ 2 * X * Q := by
            calc
              (Q : Real) ≤ X * Q :=
                le_mul_of_one_le_left (by positivity) hXReal
              _ ≤ 2 * (X * Q) :=
                le_mul_of_one_le_left (by positivity) (by norm_num)
              _ = 2 * X * Q := by ring
          simpa only [add_comm] using
            add_le_add_left (Real.log_le_log hQReal hQarg) 1
        have hlogNonneg : 1 ≤ 1 + Real.log (2 * (X : Real) * Q) := by
          have harg : (1 : Real) ≤ 2 * X * Q := by
            have hargNat : 1 ≤ 2 * X * Q := by
              have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < (2 : Nat))
                (by omega : 0 < X)) (by omega : 0 < Q)
              omega
            exact_mod_cast hargNat
          linarith [Real.log_nonneg harg]
        have hYleX : (Y : Real) ≤ X := by exact_mod_cast hYX
        have hnonnegX : (0 : Real) ≤ X := by positivity
        have hnonnegY : (0 : Real) ≤ Y := by positivity
        have hnonnegLog : 0 ≤ 1 + Real.log (2 * (X : Real) * Q) :=
          zero_le_one.trans hlogNonneg
        have hblockCountCast : (((X / L : Nat) + 1 : Nat) : Real) ≤
            3 * (X : Real) / Q + 1 := by
          simpa only [Nat.cast_add, Nat.cast_one] using hblockCount
        have hblockTerm :
            2 * (Y : Real) + 2 * Q * (1 + Real.log Q) ≤
              2 * Y + 2 * Q * (1 + Real.log (2 * X * Q)) := by
          have htwoQNonneg : (0 : Real) ≤ 2 * (Q : Real) := by
            exact mul_nonneg (by norm_num) (Nat.cast_nonneg Q)
          have hscaled :
              2 * (Q : Real) * (1 + Real.log Q) ≤
                2 * (Q : Real) * (1 + Real.log (2 * X * Q)) :=
            mul_le_mul_of_nonneg_left hlogQ htwoQNonneg
          calc
            2 * (Y : Real) + 2 * Q * (1 + Real.log Q) =
                2 * Q * (1 + Real.log Q) + 2 * Y := by ring
            _ ≤ 2 * Q * (1 + Real.log (2 * X * Q)) + 2 * Y :=
              add_le_add_left hscaled _
            _ = 2 * Y + 2 * Q * (1 + Real.log (2 * X * Q)) := by ring
        calc
          (((X / L : Nat) + 1 : Nat) : Real) *
              (2 * (Y : Real) + 2 * Q * (1 + Real.log Q)) ≤
            (3 * (X : Real) / Q + 1) *
              (2 * Y + 2 * Q * (1 + Real.log (2 * X * Q))) := by
            exact mul_le_mul hblockCountCast hblockTerm (by positivity) (by positivity)
          _ ≤ 64 * ((X : Real) * Y / Q + X + Q) *
              (1 + Real.log (2 * X * Q)) := by
            let W : Real := 1 + Real.log (2 * X * Q)
            have hW : (1 : Real) ≤ W := by simpa only [W] using hlogNonneg
            change (3 * (X : Real) / Q + 1) *
                (2 * Y + 2 * Q * W) ≤
              64 * ((X : Real) * Y / Q + X + Q) * W
            have hleft : ((3 * (X : Real) / Q + 1) *
                (2 * Y + 2 * Q * W)) * Q =
              (3 * X + Q) * (2 * Y + 2 * Q * W) := by
              field_simp [ne_of_gt hQReal]
              <;> ring
            have hright : (64 * ((X : Real) * Y / Q + X + Q) * W) * Q =
                64 * (X * Y + X * Q + Q ^ 2) * W := by
              field_simp [ne_of_gt hQReal]
              <;> ring
            apply (mul_le_mul_iff_left₀ hQReal).mp
            rw [hleft, hright]
            have hXYW : (X : Real) * Y ≤ X * Y * W :=
              le_mul_of_one_le_right (mul_nonneg hnonnegX hnonnegY) hW
            have hQY : (Q : Real) * Y ≤ Q * X := by gcongr
            have hQXW : (Q : Real) * X ≤ Q * X * W :=
              le_mul_of_one_le_right (by positivity) hW
            have hXYW0 : (0 : Real) ≤ X * Y * W := by positivity
            have hQXW0 : (0 : Real) ≤ Q * X * W := by positivity
            have hQQW0 : (0 : Real) ≤ Q ^ 2 * W := by positivity
            nlinarith

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
  classical
  have hfac : 0 < Nat.factorial k := Nat.factorial_pos k
  have himage : factorialMultiples k X ⊆ Icc 1 (Nat.factorial k * X) := by
    intro x hx
    rw [factorialMultiples, mem_image] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    rw [mem_Icc]
    have hnIcc := mem_Icc.mp hn
    exact ⟨one_le_mul hfac hnIcc.1,
      Nat.mul_le_mul_left _ hnIcc.2⟩
  calc
    (∑ n ∈ Icc 1 X,
        geometricSumMajorant t (alpha * (Nat.factorial k : Real) * n)) =
        ∑ x ∈ factorialMultiples k X,
          geometricSumMajorant t (alpha * x) := by
      rw [factorialMultiples, sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        apply congrArg (geometricSumMajorant t)
        push_cast
        ring
      · intro x hx y hy hxy
        exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) hxy
    _ ≤ ∑ x ∈ Icc 1 (Nat.factorial k * X),
          geometricSumMajorant t (alpha * x) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro x hx hnot
      exact geometricSumMajorant_nonneg _ _

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
  exact rational_geometric_sum_le X t hX ht htX a q alpha hq haq halpha

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

private def weylDifferencingPower (k : Nat) : Nat := 2 ^ (k - 1)

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
      <;> ring

private def weylRaisedCoefficientAt (k m : Nat) : Real :=
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
        <;> ring
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
  classical
  simp only [finiteDifferenceSum, differenceBounds, iteratedRealDifference]
  unfold weylSum
  symm
  refine Finset.sum_bij'
    (s := Icc (1 : Nat) t) (t := Icc (1 : Int) (t : Int))
    (fun n _ => (n : Int)) (fun z _ => z.toNat) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_Icc] at hn ⊢
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  · intro z hz
    rw [mem_Icc] at hz ⊢
    have hzNonneg : 0 ≤ z := by omega
    constructor
    · have hlow : (1 : Int) ≤ (z.toNat : Int) := by
        simpa only [Int.toNat_of_nonneg hzNonneg] using hz.1
      exact_mod_cast hlow
    · have hupp : (z.toNat : Int) ≤ (t : Int) := by
        simpa only [Int.toNat_of_nonneg hzNonneg] using hz.2
      exact_mod_cast hupp
  · intro n hn
    simp
  · intro z hz
    have hzOne : (1 : Int) ≤ z := (mem_Icc.mp hz).1
    have hzNonneg : 0 ≤ z := by omega
    simpa only [Int.toNat_of_nonneg hzNonneg]
  · intro n hn
    push_cast <;> rfl

private def weylRationalFactor (k t : Nat) (q : Int) : Real :=
  (q : Real)⁻¹ + (t : Real)⁻¹ +
    (q : Real) * (t : Real) ^ (-(k : Real))

private lemma weylRationalFactor_nonneg {k t : Nat} {q : Int}
    (hq : 0 < q) : 0 ≤ weylRationalFactor k t q := by
  unfold weylRationalFactor
  positivity

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
  rw [hpred]
  rw [div_eq_mul_inv]
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
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg htReal
  have hfac : Nat.factorial k ≤ t ^ k := by
    exact Nat.factorial_le_pow k |>.trans
      (Nat.pow_le_pow_left hk k)
  have hrpow : t ^ (k - 1) ≤ t ^ k := by
    exact Nat.pow_le_pow_right (by omega) (Nat.sub_le k 1)
  have hargNat :
      2 * (Nat.factorial k * t ^ (k - 1)) * q.natAbs ≤
        t ^ (3 * k + 1) := by
    have hqNat : q.natAbs ≤ t ^ k := by
      have hqCast : (q.natAbs : Int) = q := by
        rw [Int.natCast_natAbs, abs_of_pos hq]
      have hcast : (q.natAbs : Int) ≤ ((t ^ k : Nat) : Int) := by
        simpa only [hqCast] using hqt
      exact_mod_cast hcast
    calc
      2 * (Nat.factorial k * t ^ (k - 1)) * q.natAbs ≤
          t * (t ^ k * t ^ k) * t ^ k := by
        exact Nat.mul_le_mul (Nat.mul_le_mul ht
          (Nat.mul_le_mul hfac hrpow)) hqNat
      _ = t ^ (3 * k + 1) := by
        rw [show 3 * k + 1 = k + k + k + 1 by omega]
        simp only [pow_add, pow_one]
        ring
  have harg :
      (2 : Real) * (Nat.factorial k * t ^ (k - 1) : Nat) * q ≤
        (t : Real) ^ (3 * k + 1) := by
    have hqCast : (q.natAbs : Int) = q := by
      rw [Int.natCast_natAbs, abs_of_pos hq]
    have hqReal : (q : Real) = (q.natAbs : Nat) := by
      have hcast := congrArg (fun z : Int => (z : Real)) hqCast
      simpa only [Int.cast_natCast] using hcast.symm
    rw [hqReal]
    exact_mod_cast hargNat
  have hargPos : (0 : Real) <
      2 * (Nat.factorial k * t ^ (k - 1) : Nat) * q := by positivity
  calc
    1 + Real.log
        (2 * (Nat.factorial k * t ^ (k - 1) : Nat) * (q : Real)) ≤
        1 + Real.log ((t : Real) ^ (3 * k + 1)) := by
      simpa only [add_comm] using
        add_le_add_left (Real.log_le_log hargPos harg) 1
    _ = 1 + (3 * k + 1 : Nat) * Real.log t := by
      rw [Real.log_pow]
    _ ≤ 4 * (k + 1 : Nat) * (1 + Real.log t) := by
      push_cast <;> nlinarith

/-!
This is the quantitative raised form of Weyl's inequality.  All constants
before the final `2^(k-1)`-st root are visible.  The hypotheses `2 ≤ t` and
`k ≤ t` are harmless both for the asymptotic and repaired explicit forms.
-/

private theorem weyl_raised_estimate {alpha : Real} {k t m : Nat}
    (hk : 2 ≤ k) (ht : 2 ≤ t) (hkt : k ≤ t) (hm : 1 ≤ m)
    (a q : Int) (hq : 0 < q) (haq : Int.gcd a q = 1)
    (halpha : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹) :
    ‖weylSum alpha k t‖ ^ weylDifferencingPower k ≤
      weylRaisedCoefficientAt k m *
        (t : Real) ^ ((weylDifferencingPower k : Real) +
          (((k - 1 : Nat) : Real) ^ 2) / m) *
        weylRationalFactor k t q * (1 + Real.log t) := by
  let r := k - 1
  let K := weylDifferencingPower k
  let E := weylCauchyExponent r
  let D : Real := (weylShiftRange t).card
  let eta : Real := ((r : Real) ^ 2) / m
  let B := weylRationalFactor k t q
  let L : Real := 1 + Real.log t
  have hr : 1 ≤ r := by dsimp only [r]; omega
  have hK : K = 2 ^ r := by rfl
  have hKge : k ≤ K := by
    dsimp only [K, r, weylDifferencingPower]
    have hs := nat_succ_le_two_pow (k - 1)
    omega
  have hE : E = K - k := by
    have hkr : k = r + 1 := by dsimp only [r]; omega
    dsimp only [E]
    rw [weylCauchyExponent_eq]
    rw [hK, hkr]
    omega
  have hD : D ≤ 2 * t := by
    dsimp only [D]
    exact_mod_cast weylShiftRange_card_le t
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact_mod_cast Nat.zero_le (weylShiftRange t).card
  have htOne : 1 ≤ t := ht.trans' (by norm_num)
  have htReal : (1 : Real) ≤ t := by exact_mod_cast htOne
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg htReal]
  have hB : 0 ≤ B := weylRationalFactor_nonneg hq
  have hBInv : (t : Real)⁻¹ ≤ B := by
    dsimp only [B]
    unfold weylRationalFactor
    have hqNonneg : (0 : Real) ≤ q := by exact_mod_cast hq.le
    have hqInvNonneg : (0 : Real) ≤ (q : Real)⁻¹ := inv_nonneg.mpr hqNonneg
    have hlastNonneg : (0 : Real) ≤
        (q : Real) * (t : Real) ^ (-(k : Real)) :=
      mul_nonneg hqNonneg (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le t) _)
    linarith
  have heta : 0 ≤ eta := by
    dsimp only [eta]
    exact div_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le m)
  have hbase := finiteDifferenceSum_iterated_le
    (fun z => alpha * (z : Real) ^ k) t r []
  rw [finiteDifferenceSum_nil_eq_weylSum] at hbase
  have hsplit := iteratedDifferenceNormSum_split_zero
    (fun z => alpha * (z : Real) ^ k) htOne r []
  have hnz := iteratedNonzeroDifferenceNormSum_le_positive
    (alpha := alpha) (k := k) (t := t) (j := r) (hs := [])
    (by omega : 1 ≤ k) (by simp [r])
  have hzeroLoss := weylZeroContribution_le t r
  have htargetBase :
      (t : Real) ^ (K - 1) ≤
        (t : Real) ^ ((K : Real) + eta) * B * L := by
    have hKOne : 1 ≤ K := by
      dsimp only [K, weylDifferencingPower]
      exact one_le_pow₀ (by norm_num)
    have hpow : (t : Real) ^ (K - 1) ≤
        (t : Real) ^ ((K : Real) + eta) * (t : Real)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg_one,
        ← Real.rpow_add (by positivity)]
      apply Real.rpow_le_rpow_of_exponent_le htReal
      rw [Nat.cast_sub hKOne]
      push_cast
      linarith
    calc
      _ ≤ (t : Real) ^ ((K : Real) + eta) * (t : Real)⁻¹ := hpow
      _ ≤ (t : Real) ^ ((K : Real) + eta) * B := by
        exact mul_le_mul_of_nonneg_left hBInv (by positivity)
      _ ≤ (t : Real) ^ ((K : Real) + eta) * B * L := by
        exact le_mul_of_one_le_right (mul_nonneg (by positivity) hB) hL
  have hzeroTerm :
      D ^ E * weylZeroContribution t r ≤
        (2 : Real) ^ K * k *
          ((t : Real) ^ ((K : Real) + eta) * B * L) := by
    calc
      D ^ E * weylZeroContribution t r ≤
          D ^ E * ((r : Real) * t * D ^ (r - 1)) := by
        exact mul_le_mul_of_nonneg_left hzeroLoss (pow_nonneg hD0 E)
      _ = (r : Real) * t * D ^ (K - 2) := by
        calc
          D ^ E * ((r : Real) * t * D ^ (r - 1)) =
              (r : Real) * t * (D ^ E * D ^ (r - 1)) := by ring
          _ = (r : Real) * t * D ^ (E + (r - 1)) := by rw [← pow_add]
          _ = (r : Real) * t * D ^ (K - 2) := by
            congr 2
            rw [hE]
            omega
      _ ≤ (r : Real) * t * (2 * t : Real) ^ (K - 2) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hD0 hD (K - 2)) (by positivity)
      _ = (r : Real) * (2 : Real) ^ (K - 2) *
          (t : Real) ^ (K - 1) := by
        rw [mul_pow]
        have hKtwo : 2 ≤ K := by
          exact hk.trans hKge
        have hpowT : (t : Real) ^ (K - 2) * t =
            (t : Real) ^ (K - 1) := by
          rw [← pow_succ]
          congr 1
          omega
        calc
          (r : Real) * t *
              ((2 : Real) ^ (K - 2) * (t : Real) ^ (K - 2)) =
              (r : Real) * (2 : Real) ^ (K - 2) *
                ((t : Real) ^ (K - 2) * t) := by ring
          _ = (r : Real) * (2 : Real) ^ (K - 2) *
                (t : Real) ^ (K - 1) := by rw [hpowT]
      _ ≤ (2 : Real) ^ K * k * (t : Real) ^ (K - 1) := by
        have hrk : (r : Real) ≤ k := by exact_mod_cast Nat.sub_le k 1
        have hpow : (2 : Real) ^ (K - 2) ≤ 2 ^ K := by
          exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le K 2)
        have hcoeff : (r : Real) * (2 : Real) ^ (K - 2) ≤
            (2 : Real) ^ K * k := by
          calc
            (r : Real) * (2 : Real) ^ (K - 2) ≤
                k * (2 : Real) ^ (K - 2) :=
              mul_le_mul_of_nonneg_right hrk (by positivity)
            _ ≤ k * (2 : Real) ^ K :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
            _ = (2 : Real) ^ K * k := by ring
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ ≤ (2 : Real) ^ K * k *
          ((t : Real) ^ ((K : Real) + eta) * B * L) := by
        exact mul_le_mul_of_nonneg_left htargetBase (by positivity)
  by_cases hqLarge : (t ^ k : Nat) < q
  · have hBOne : 1 ≤ B := by
      have hqtk : (1 : Real) < (q : Real) * (t : Real) ^ (-(k : Real)) := by
        have hqtReal : (t : Real) ^ k < q := by exact_mod_cast hqLarge
        rw [← Real.rpow_natCast] at hqtReal
        rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv]
        exact (lt_div_iff₀ (by positivity)).2 (by
          simpa only [one_mul] using hqtReal)
      dsimp only [B]
      unfold weylRationalFactor
      have hinvq : (0 : Real) ≤ (q : Real)⁻¹ := by positivity
      have hinvt : (0 : Real) ≤ (t : Real)⁻¹ := by positivity
      linarith
    have hcoeff : 1 ≤ weylRaisedCoefficientAt k m := by
      unfold weylRaisedCoefficientAt
      dsimp only
      have hmReal : (1 : Real) ≤ m := by exact_mod_cast hm
      have hfac : (1 : Real) ≤ Nat.factorial k := by
        exact_mod_cast (show 1 ≤ Nat.factorial k from Nat.factorial_pos k)
      have htwo : (1 : Real) ≤ 2 ^ (K + 2 * k + 12) :=
        one_le_pow₀ (by norm_num)
      have hmpow : (1 : Real) ≤ (m : Real) ^ ((k - 1) * 2 ^ m) :=
        one_le_pow₀ hmReal
      have hkplus : (1 : Real) ≤ k + 1 := by exact_mod_cast Nat.succ_pos k
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le htwo hfac) hmpow) hkplus
    calc
      ‖weylSum alpha k t‖ ^ K ≤ (t : Real) ^ K := by
        exact pow_le_pow_left₀ (norm_nonneg _) (weylSum_norm_le alpha k t) K
      _ ≤ (t : Real) ^ ((K : Real) + eta) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le htReal (by linarith [heta])
      _ ≤ weylRaisedCoefficientAt k m *
          (t : Real) ^ ((K : Real) + eta) * B * L := by
        have hp : 0 ≤ (t : Real) ^ ((K : Real) + eta) := by positivity
        calc
          (t : Real) ^ ((K : Real) + eta) ≤
              weylRaisedCoefficientAt k m *
                (t : Real) ^ ((K : Real) + eta) :=
            le_mul_of_one_le_left hp hcoeff
          _ ≤ weylRaisedCoefficientAt k m *
                (t : Real) ^ ((K : Real) + eta) * B :=
            le_mul_of_one_le_right (mul_nonneg (by positivity) hp) hBOne
          _ ≤ weylRaisedCoefficientAt k m *
                (t : Real) ^ ((K : Real) + eta) * B * L :=
            le_mul_of_one_le_right (mul_nonneg (by positivity) hB) hL
  · have hqt : q ≤ (t ^ k : Nat) := by
      exact le_of_not_gt hqLarge
    have hterminal := terminal_positive_sum_rational_bound
      (alpha := alpha) (k := k) (t := t) (r := r) (m := m)
      hm htOne hr a q hq haq halpha
    have hloss := divisorMultiplicityLoss_eq
      (m := m) (r := r) (t := t) hm htOne
    have hlog := terminal_log_le hkt ht hq hqt
    have hbracket :
        (((Nat.factorial k * t ^ r : Nat) : Real) * t / q +
              (Nat.factorial k * t ^ r : Nat) + q) ≤
          (Nat.factorial k : Real) *
            ((t : Real) ^ k * B) := by
      rw [pow_mul_weylRationalFactor (by omega : 1 ≤ k) htOne q]
      have hfacOne : (1 : Real) ≤ Nat.factorial k := by
        exact_mod_cast (show 1 ≤ Nat.factorial k from Nat.factorial_pos k)
      have hrk : r + 1 = k := by dsimp only [r]; omega
      push_cast
      have htpow : (t : Real) ^ r * (t : Real) = (t : Real) ^ k := by
        rw [← pow_succ, hrk]
      have htr : (t : Real) ^ r = (t : Real) ^ (k - 1) := by
        dsimp only [r]
      have hqNonneg : (0 : Real) ≤ q := by positivity
      have hqScale : (q : Real) ≤ (Nat.factorial k : Real) * q :=
        le_mul_of_one_le_left hqNonneg hfacOne
      calc
        (Nat.factorial k : Real) * (t : Real) ^ r * (t : Real) / q +
              (Nat.factorial k : Real) * (t : Real) ^ r + q =
            (Nat.factorial k : Real) *
                (((t : Real) ^ r * (t : Real)) / q + (t : Real) ^ r) + q := by
          ring
        _ = (Nat.factorial k : Real) *
              ((t : Real) ^ k / q + (t : Real) ^ (k - 1)) + q := by
          rw [htpow, htr]
        _ ≤ (Nat.factorial k : Real) *
              ((t : Real) ^ k / q + (t : Real) ^ (k - 1)) +
                (Nat.factorial k : Real) * q := by
          calc
            (Nat.factorial k : Real) *
                  ((t : Real) ^ k / q + (t : Real) ^ (k - 1)) + q =
                q + (Nat.factorial k : Real) *
                  ((t : Real) ^ k / q + (t : Real) ^ (k - 1)) := by ring
            _ ≤ (Nat.factorial k : Real) * q +
                (Nat.factorial k : Real) *
                  ((t : Real) ^ k / q + (t : Real) ^ (k - 1)) :=
              add_le_add_left hqScale _
            _ = (Nat.factorial k : Real) *
                  ((t : Real) ^ k / q + (t : Real) ^ (k - 1)) +
                (Nat.factorial k : Real) * q := by ring
        _ = (Nat.factorial k : Real) *
              ((t : Real) ^ k / q + (t : Real) ^ (k - 1) + q) := by
          ring
    have hnzTerm :
        D ^ E * (2 : Real) ^ r *
            positiveProductMajorantSum alpha k t r 1 ≤
          (2 : Real) ^ (K + 7) * Nat.factorial k *
            (m : Real) ^ (r * 2 ^ m) * (k + 1) *
            ((t : Real) ^ ((K : Real) + eta) * B * L) := by
      have hterminalArgOne : (1 : Real) ≤
          2 * (Nat.factorial k * t ^ r : Nat) * q := by
        have hfacPowOne : 1 ≤ Nat.factorial k * t ^ r :=
          one_le_mul (Nat.factorial_pos k) (one_le_pow₀ htOne)
        have hfacPowOneReal : (1 : Real) ≤
            (Nat.factorial k * t ^ r : Nat) := by exact_mod_cast hfacPowOne
        have hqOneReal : (1 : Real) ≤ q := by
          exact_mod_cast (show (1 : Int) ≤ q by omega)
        calc
          (1 : Real) ≤ 2 * 1 * 1 := by norm_num
          _ ≤ 2 * (Nat.factorial k * t ^ r : Nat) * q := by gcongr
      have hterminalLogNonneg : 0 ≤
          1 + Real.log (2 * (Nat.factorial k * t ^ r : Nat) * q) := by
        linarith [Real.log_nonneg hterminalArgOne]
      have hinside :
          64 * (((Nat.factorial k * t ^ r : Nat) : Real) * t / q +
              (Nat.factorial k * t ^ r : Nat) + q) *
              (1 + Real.log
                (2 * (Nat.factorial k * t ^ r : Nat) * q)) ≤
            64 * ((Nat.factorial k : Real) * ((t : Real) ^ k * B)) *
              (4 * (k + 1 : Nat) * L) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hbracket (by norm_num)
        · exact hlog
        · exact hterminalLogNonneg
        · positivity
      calc
        D ^ E * (2 : Real) ^ r *
            positiveProductMajorantSum alpha k t r 1 ≤
          D ^ E * 2 ^ r *
            (divisorMultiplicityLoss m r t *
              (64 * (((Nat.factorial k * t ^ r : Nat) : Real) * t / q +
                  (Nat.factorial k * t ^ r : Nat) + q) *
                (1 + Real.log
                  (2 * (Nat.factorial k * t ^ r : Nat) * q)))) := by
          exact mul_le_mul_of_nonneg_left hterminal
            (mul_nonneg (pow_nonneg hD0 E) (by positivity))
        _ ≤ D ^ E * 2 ^ r *
            (((m : Real) ^ (r * 2 ^ m) * (t : Real) ^ eta) *
              (64 * ((Nat.factorial k : Real) * ((t : Real) ^ k * B)) *
                (4 * (k + 1 : Nat) * L))) := by
          rw [hloss]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinside (by positivity))
            (mul_nonneg (pow_nonneg hD0 E) (by positivity))
        _ ≤ (2 * t : Real) ^ E * 2 ^ r *
            (((m : Real) ^ (r * 2 ^ m) * (t : Real) ^ eta) *
              (64 * ((Nat.factorial k : Real) * ((t : Real) ^ k * B)) *
                (4 * (k + 1 : Nat) * L))) := by
          have hpowD : D ^ E ≤ (2 * t : Real) ^ E :=
            pow_le_pow_left₀ hD0 hD E
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpowD (by positivity)) (by positivity)
        _ = (2 : Real) ^ (K + 7) * Nat.factorial k *
            (m : Real) ^ (r * 2 ^ m) * (k + 1) *
            ((t : Real) ^ ((K : Real) + eta) * B * L) := by
          have hEk : E + k = K := by rw [hE]; omega
          have htwoCombine :
              (2 : Real) ^ E * (2 : Real) ^ r * 64 * 4 =
                (2 : Real) ^ (K + 7) := by
            rw [show (64 : Real) = 2 ^ 6 by norm_num,
              show (4 : Real) = 2 ^ 2 by norm_num,
              ← pow_add, ← pow_add, ← pow_add]
            congr 1
            rw [hE]
            dsimp only [r]
            omega
          have htCombine :
              (t : Real) ^ E * (t : Real) ^ eta * (t : Real) ^ k =
                (t : Real) ^ ((K : Real) + eta) := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast]
            calc
              (t : Real) ^ (E : Real) * (t : Real) ^ eta *
                  (t : Real) ^ (k : Real) =
                  (t : Real) ^ ((E : Real) + eta + k) := by
                rw [Real.rpow_add (by positivity),
                  Real.rpow_add (by positivity)]
              _ = (t : Real) ^ ((K : Real) + eta) := by
                congr 1
                have hEkReal : (E : Real) + k = K := by exact_mod_cast hEk
                linarith
          rw [mul_pow]
          calc
            (2 : Real) ^ E * (t : Real) ^ E * 2 ^ r *
                (((m : Real) ^ (r * 2 ^ m) * (t : Real) ^ eta) *
                  (64 * ((Nat.factorial k : Real) * ((t : Real) ^ k * B)) *
                    (4 * (k + 1 : Nat) * L))) =
                ((2 : Real) ^ E * (2 : Real) ^ r * 64 * 4) *
                  Nat.factorial k * (m : Real) ^ (r * 2 ^ m) * (k + 1) *
                    (((t : Real) ^ E * (t : Real) ^ eta * (t : Real) ^ k) *
              B * L) := by
              push_cast
              ac_rfl
            _ = (2 : Real) ^ (K + 7) * Nat.factorial k *
                (m : Real) ^ (r * 2 ^ m) * (k + 1) *
                  ((t : Real) ^ ((K : Real) + eta) * B * L) := by
              rw [htwoCombine, htCombine]
    calc
      ‖weylSum alpha k t‖ ^ K ≤
          D ^ E * iteratedDifferenceNormSum
            (fun z => alpha * (z : Real) ^ k) t r [] := by
        simpa only [K, E, D, hK] using hbase
      _ ≤ D ^ E *
          (weylZeroContribution t r +
            iteratedNonzeroDifferenceNormSum
              (fun z => alpha * (z : Real) ^ k) t r []) := by
        exact mul_le_mul_of_nonneg_left hsplit (pow_nonneg hD0 E)
      _ ≤ D ^ E *
          (weylZeroContribution t r +
            (2 : Real) ^ r * positiveProductMajorantSum alpha k t r 1) := by
        have hnz' :
            iteratedNonzeroDifferenceNormSum
                (fun z => alpha * (z : Real) ^ k) t r [] ≤
              (2 : Real) ^ r * positiveProductMajorantSum alpha k t r 1 := by
          simpa only [natAbsShiftProduct, List.map_nil, List.prod_nil] using hnz
        have hadd :
            weylZeroContribution t r +
                iteratedNonzeroDifferenceNormSum
                  (fun z => alpha * (z : Real) ^ k) t r [] ≤
              weylZeroContribution t r +
                (2 : Real) ^ r * positiveProductMajorantSum alpha k t r 1 := by
          calc
            weylZeroContribution t r +
                  iteratedNonzeroDifferenceNormSum
                    (fun z => alpha * (z : Real) ^ k) t r [] =
                iteratedNonzeroDifferenceNormSum
                    (fun z => alpha * (z : Real) ^ k) t r [] +
                  weylZeroContribution t r := by ring
            _ ≤ (2 : Real) ^ r * positiveProductMajorantSum alpha k t r 1 +
                weylZeroContribution t r := add_le_add_left hnz' _
            _ = weylZeroContribution t r +
                (2 : Real) ^ r * positiveProductMajorantSum alpha k t r 1 := by ring
        exact mul_le_mul_of_nonneg_left
          hadd (pow_nonneg hD0 E)
      _ = D ^ E * weylZeroContribution t r +
          D ^ E * 2 ^ r * positiveProductMajorantSum alpha k t r 1 := by ring
      _ ≤ (2 : Real) ^ K * k *
            ((t : Real) ^ ((K : Real) + eta) * B * L) +
          (2 : Real) ^ (K + 7) * Nat.factorial k *
            (m : Real) ^ (r * 2 ^ m) * (k + 1) *
            ((t : Real) ^ ((K : Real) + eta) * B * L) :=
        add_le_add hzeroTerm hnzTerm
      _ ≤ weylRaisedCoefficientAt k m *
          (t : Real) ^ ((K : Real) + eta) * B * L := by
        unfold weylRaisedCoefficientAt
        dsimp only [K]
        have hcommon : 0 ≤
            (t : Real) ^ ((K : Real) + eta) * B * L := by positivity
        have hfacOne : (1 : Real) ≤ Nat.factorial k := by
          exact_mod_cast (show 1 ≤ Nat.factorial k from Nat.factorial_pos k)
        have hmOne : (1 : Real) ≤ (m : Real) ^ (r * 2 ^ m) := by
          exact one_le_pow₀ (by exact_mod_cast hm)
        have hextra : (1 : Real) ≤
            (Nat.factorial k : Real) * (m : Real) ^ (r * 2 ^ m) :=
          one_le_mul_of_one_le_of_one_le hfacOne hmOne
        have hzeroCoefficient : (2 : Real) ^ K * k ≤
            (2 : Real) ^ (K + 2 * k + 11) * Nat.factorial k *
              m ^ (r * 2 ^ m) * (k + 1) := by
          have htwoPow : (2 : Real) ^ K ≤
              (2 : Real) ^ (K + 2 * k + 11) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          calc
            (2 : Real) ^ K * k ≤
                (2 : Real) ^ (K + 2 * k + 11) * k := by
              exact mul_le_mul_of_nonneg_right htwoPow (by positivity)
            _ ≤ (2 : Real) ^ (K + 2 * k + 11) * (k + 1) := by
              exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k)
                (by positivity)
            _ ≤ (2 : Real) ^ (K + 2 * k + 11) *
                ((Nat.factorial k : Real) * m ^ (r * 2 ^ m) * (k + 1)) := by
              have hextraScaled : (k : Real) + 1 ≤
                  ((Nat.factorial k : Real) * m ^ (r * 2 ^ m)) *
                    ((k : Real) + 1) := by
                simpa only [one_mul] using
                  (mul_le_mul_of_nonneg_right hextra
                    (show (0 : Real) ≤ (k : Real) + 1 by positivity))
              exact mul_le_mul_of_nonneg_left
                hextraScaled (by positivity)
            _ = (2 : Real) ^ (K + 2 * k + 11) * Nat.factorial k *
                m ^ (r * 2 ^ m) * (k + 1) := by ring
        have hnonzeroCoefficient :
            (2 : Real) ^ (K + 7) * Nat.factorial k *
                m ^ (r * 2 ^ m) * (k + 1) ≤
              (2 : Real) ^ (K + 2 * k + 11) * Nat.factorial k *
                m ^ (r * 2 ^ m) * (k + 1) := by
          have htwoPow : (2 : Real) ^ (K + 7) ≤
              (2 : Real) ^ (K + 2 * k + 11) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right htwoPow (by positivity))
              (by positivity)) (by positivity)
        have hdouble : (2 : Real) ^ (K + 2 * k + 12) =
            2 * (2 : Real) ^ (K + 2 * k + 11) := by
          rw [show K + 2 * k + 12 = (K + 2 * k + 11) + 1 by omega,
            pow_succ]
          ring
        calc
          (2 : Real) ^ K * k *
                ((t : Real) ^ ((K : Real) + eta) * B * L) +
              (2 : Real) ^ (K + 7) * Nat.factorial k *
                m ^ (r * 2 ^ m) * (k + 1) *
                ((t : Real) ^ ((K : Real) + eta) * B * L) =
            ((2 : Real) ^ K * k +
              (2 : Real) ^ (K + 7) * Nat.factorial k *
                m ^ (r * 2 ^ m) * (k + 1)) *
              ((t : Real) ^ ((K : Real) + eta) * B * L) := by
            rw [add_mul]
          _ ≤
            ((2 : Real) ^ (K + 2 * k + 11) * Nat.factorial k *
                m ^ (r * 2 ^ m) * (k + 1) +
              (2 : Real) ^ (K + 2 * k + 11) * Nat.factorial k *
                m ^ (r * 2 ^ m) * (k + 1)) *
              ((t : Real) ^ ((K : Real) + eta) * B * L) := by
            exact mul_le_mul_of_nonneg_right
              (add_le_add hzeroCoefficient hnonzeroCoefficient) hcommon
          _ = (2 : Real) ^ (K + 2 * k + 12) * Nat.factorial k *
              m ^ (r * 2 ^ m) * (k + 1) *
                (t : Real) ^ ((K : Real) + eta) * B * L := by
            rw [hdouble]
            ring

private lemma weylSum_degree_one_le_geometric (alpha : Real) (t : Nat) :
    ‖weylSum alpha 1 t‖ ≤ geometricSumMajorant t alpha := by
  classical
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
  by_cases ht0 : t = 0
  · subst t
    simp [weylSum]
  have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
  have hfactor : (t : Real) * weylRationalFactor 1 t q =
      (t : Real) / q + 1 + q := by
    simpa only [pow_one, Nat.sub_self, pow_zero] using
      pow_mul_weylRationalFactor (k := 1) (t := t) (by norm_num) ht q
  rw [hfactor]
  refine (weylSum_degree_one_le_geometric alpha t).trans ?_
  by_cases hqOne : q = 1
  · subst q
    refine (geometricSumMajorant_le_length t alpha).trans ?_
    have htNonneg : (0 : Real) ≤ t := by positivity
    norm_num only [Int.cast_one, div_one]
    linarith
  · have hqTwo : (2 : Int) ≤ q := by omega
    have hsep := nearby_rational_phase_separated hq haq halpha
      (show (1 : Nat) ≠ 0 by omega)
      (show |((1 : Nat) : Int) - 0| ≤ q / 2 by
        simp only [Nat.cast_one, Nat.cast_zero, sub_zero, abs_one]
        exact Int.le_ediv_iff_mul_le (by norm_num) |>.2 (by omega))
    have hrep0 : nearestIntegerRepresentative (alpha * (0 : Nat)) = 0 := by
      simp [nearestIntegerRepresentative]
    rw [hrep0, sub_zero, abs_nearestIntegerRepresentative] at hsep
    have hsepNorm : (2 * (q : Real))⁻¹ ≤
        ‖(alpha : UnitAddCircle)‖ := by
      simpa only [Nat.cast_one, mul_one] using hsep
    have hqReal : (0 : Real) < q := by exact_mod_cast hq
    have hdenPos : (0 : Real) < 2 * (q : Real) :=
      mul_pos (by norm_num) hqReal
    have hinvPos : (0 : Real) < (2 * (q : Real))⁻¹ := inv_pos.mpr hdenPos
    have hnorm : 0 < ‖(alpha : UnitAddCircle)‖ := hinvPos.trans_le hsepNorm
    have halpha0 : (alpha : UnitAddCircle) ≠ 0 := norm_pos_iff.mp hnorm
    unfold geometricSumMajorant
    rw [if_neg halpha0]
    refine (min_le_right _ _).trans ?_
    rw [inv_eq_one_div, div_le_iff₀ (mul_pos (by norm_num) hnorm)]
    rw [inv_eq_one_div, div_le_iff₀ (mul_pos (by norm_num) hqReal)] at hsepNorm
    have hsep' : (1 : Real) ≤ 2 * q * ‖(alpha : UnitAddCircle)‖ := by
      calc
        (1 : Real) ≤ ‖(alpha : UnitAddCircle)‖ * (2 * q) := hsepNorm
        _ = 2 * q * ‖(alpha : UnitAddCircle)‖ := by ring
    have hqBracket : (q : Real) ≤ (t : Real) / q + 1 + q := by
      have : (0 : Real) ≤ (t : Real) / q := by positivity
      linarith
    calc
      (1 : Real) ≤ 2 * q * ‖(alpha : UnitAddCircle)‖ := hsep'
      _ ≤ ((t : Real) / q + 1 + q) *
          (2 * ‖(alpha : UnitAddCircle)‖) := by
        have htwoNormNonneg : (0 : Real) ≤
            2 * ‖(alpha : UnitAddCircle)‖ :=
          mul_nonneg (by norm_num) (norm_nonneg (alpha : UnitAddCircle))
        have hmul : (q : Real) * (2 * ‖(alpha : UnitAddCircle)‖) ≤
            ((t : Real) / q + 1 + q) *
              (2 * ‖(alpha : UnitAddCircle)‖) :=
          mul_le_mul_of_nonneg_right hqBracket htwoNormNonneg
        calc
          2 * q * ‖(alpha : UnitAddCircle)‖ =
              q * (2 * ‖(alpha : UnitAddCircle)‖) := by ring
          _ ≤ ((t : Real) / q + 1 + q) *
              (2 * ‖(alpha : UnitAddCircle)‖) := hmul

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
    refine ⟨1, by norm_num, ?_⟩
    intro t a q alpha hq haq halpha
    have hone : ((2 : Real) ^ (1 - 1))⁻¹ = 1 := by norm_num
    rw [hone, Real.rpow_one]
    by_cases ht0 : t = 0
    · subst t
      have hzero : weylSum alpha 1 0 = 0 := by simp [weylSum]
      rw [hzero, norm_zero]
      simpa only [one_mul] using
        mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (weylRationalFactor_nonneg (k := 1) (t := 0) hq)
    have ht : (1 : Real) ≤ t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht0
    have hpow : (t : Real) ≤ (t : Real) ^ (1 + epsilon) := by
      calc
        (t : Real) = (t : Real) ^ (1 : Real) := by simp
        _ ≤ (t : Real) ^ (1 + epsilon) :=
          Real.rpow_le_rpow_of_exponent_le
            (x := (t : Real)) (y := (1 : Real)) (z := 1 + epsilon)
            ht (by linarith)
    calc
      ‖weylSum alpha 1 t‖ ≤ (t : Real) * weylRationalFactor 1 t q :=
        weyl_degree_one_bound t a q alpha hq haq halpha
      _ ≤ 1 * (t : Real) ^ (1 + epsilon) *
          weylRationalFactor 1 t q := by
        have hB := weylRationalFactor_nonneg (k := 1) (t := t) hq
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hB
  · have hkTwo : 2 ≤ k := by omega
    let r := k - 1
    let K := weylDifferencingPower k
    have hKposNat : 0 < K := by
      dsimp only [K, weylDifferencingPower]
      exact pow_pos (by norm_num : 0 < (2 : Nat)) _
    have hKpos : (0 : Real) < K := by exact_mod_cast hKposNat
    let delta : Real := epsilon * K / 2
    have hdelta : 0 < delta := by dsimp only [delta]; positivity
    obtain ⟨m₀ : Nat, hm₀⟩ := exists_nat_ge
      (2 * ((r : Real) ^ 2) / (epsilon * K))
    let m := m₀ + 1
    have hm : 1 ≤ m := by dsimp only [m]; omega
    have heta : ((r : Real) ^ 2) / m ≤ epsilon * K / 2 := by
      have hmReal : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
      have heK : 0 < epsilon * (K : Real) := mul_pos hepsilon hKpos
      have hm₀' : 2 * (r : Real) ^ 2 ≤
          (m₀ : Real) * (epsilon * K) :=
        (div_le_iff₀ heK).mp hm₀
      rw [div_le_iff₀ hmReal]
      dsimp only [m] at hmReal ⊢
      push_cast at hm₀' ⊢
      nlinarith
    let A : Real := weylRaisedCoefficientAt k m
    let Aeps : Real := A * (1 + delta⁻¹)
    let T : Nat := max 2 k
    let C : Real := Aeps ^ ((K : Real)⁻¹) + T + 1
    have hA : 0 ≤ A := by unfold A weylRaisedCoefficientAt; positivity
    have hAeps : 0 ≤ Aeps := by
      dsimp only [Aeps]
      exact mul_nonneg hA
        (add_nonneg zero_le_one (inv_nonneg.mpr hdelta.le))
    have hC : 0 ≤ C := by
      dsimp only [C]
      exact add_nonneg
        (add_nonneg (Real.rpow_nonneg hAeps _)
          (by exact_mod_cast Nat.zero_le T)) zero_le_one
    refine ⟨C, hC, ?_⟩
    intro t a q alpha hq haq halpha
    by_cases ht0 : t = 0
    · subst t
      have hzero : weylSum alpha k 0 = 0 := by simp [weylSum]
      rw [hzero, norm_zero]
      exact mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (weylRationalFactor_nonneg hq) _)
    have htOne : (1 : Real) ≤ t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht0
    have hB : 0 < weylRationalFactor k t q := by
      unfold weylRationalFactor
      positivity
    have hKnat : K = 2 ^ (k - 1) := rfl
    have hrootExp : ((K : Real))⁻¹ = ((2 : Real) ^ (k - 1))⁻¹ := by
      simpa only [hKnat, Nat.cast_pow, Nat.cast_ofNat]
    by_cases htLarge : T ≤ t
    · have htTwo : 2 ≤ t := (le_max_left 2 k).trans htLarge
      have hkt : k ≤ t := (le_max_right 2 k).trans htLarge
      have hraised := weyl_raised_estimate
        (alpha := alpha) (k := k) (t := t) (m := m)
        hkTwo htTwo hkt hm a q hq haq halpha
      have hlog : 1 + Real.log t ≤
          (1 + delta⁻¹) * (t : Real) ^ delta := by
        have hpowOne : 1 ≤ (t : Real) ^ delta :=
          Real.one_le_rpow htOne hdelta.le
        have hlogPow := Real.log_natCast_le_rpow_div t hdelta
        rw [div_eq_mul_inv] at hlogPow
        nlinarith [mul_nonneg (inv_nonneg.mpr hdelta.le) (by positivity :
          0 ≤ (t : Real) ^ delta)]
      have hexponent :
          (K : Real) + ((r : Real) ^ 2) / m + delta ≤
            K * (1 + epsilon) := by
        dsimp only [delta]
        nlinarith
      have hraised' : ‖weylSum alpha k t‖ ^ K ≤
          Aeps * (t : Real) ^ (K * (1 + epsilon)) *
            weylRationalFactor k t q := by
        calc
          _ ≤ A * (t : Real) ^ ((K : Real) + ((r : Real) ^ 2) / m) *
              weylRationalFactor k t q * (1 + Real.log t) := by
            simpa only [A, K, r] using hraised
          _ ≤ A * (t : Real) ^ ((K : Real) + ((r : Real) ^ 2) / m) *
              weylRationalFactor k t q *
                ((1 + delta⁻¹) * (t : Real) ^ delta) := by
            exact mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = A * (1 + delta⁻¹) *
              ((t : Real) ^ ((K : Real) + ((r : Real) ^ 2) / m) *
                (t : Real) ^ delta) * weylRationalFactor k t q := by ring
          _ = Aeps *
              (t : Real) ^
                ((K : Real) + ((r : Real) ^ 2) / m + delta) *
              weylRationalFactor k t q := by
            dsimp only [Aeps]
            rw [← Real.rpow_add (by positivity)]
          _ ≤ Aeps * (t : Real) ^ (K * (1 + epsilon)) *
              weylRationalFactor k t q := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le htOne hexponent) hAeps)
              (by positivity)
      have hroot : ‖weylSum alpha k t‖ ≤
          (Aeps * (t : Real) ^ (K * (1 + epsilon)) *
            weylRationalFactor k t q) ^ ((K : Real))⁻¹ :=
        (Real.le_rpow_inv_iff_of_pos
          (x := ‖weylSum alpha k t‖)
          (y := Aeps * (t : Real) ^ (K * (1 + epsilon)) *
            weylRationalFactor k t q)
          (z := (K : Real)) (norm_nonneg _) (by positivity) hKpos).2 (by
            simpa only [Real.rpow_natCast] using hraised')
      have hKcancel : (K : Real) * (K : Real)⁻¹ = 1 :=
        mul_inv_cancel₀ hKpos.ne'
      have htexp :
          (((t : Real) ^ (K * (1 + epsilon))) ^ ((K : Real))⁻¹) =
            (t : Real) ^ (1 + epsilon) := by
        rw [← Real.rpow_mul (by positivity)]
        congr 1
        calc
          (K : Real) * (1 + epsilon) * (K : Real)⁻¹ =
              ((K : Real) * (K : Real)⁻¹) * (1 + epsilon) := by ring
          _ = 1 + epsilon := by rw [hKcancel, one_mul]
      calc
        ‖weylSum alpha k t‖ ≤
            (Aeps * (t : Real) ^ (K * (1 + epsilon)) *
              weylRationalFactor k t q) ^ ((K : Real))⁻¹ := hroot
        _ = Aeps ^ ((K : Real))⁻¹ *
              (t : Real) ^ (1 + epsilon) *
              weylRationalFactor k t q ^ ((K : Real))⁻¹ := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity), htexp]
        _ ≤ C * (t : Real) ^ (1 + epsilon) *
              (weylRationalFactor k t q ^
                ((2 : Real) ^ (k - 1))⁻¹) := by
          rw [← hrootExp]
          have hAC : Aeps ^ ((K : Real))⁻¹ ≤ C := by
            dsimp only [C]
            linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hAC (by positivity)) (by positivity)
    · have htT : t < T := by omega
      have hBinv : (t : Real)⁻¹ ≤ weylRationalFactor k t q := by
        unfold weylRationalFactor
        have hqNonneg : (0 : Real) ≤ q := by exact_mod_cast hq.le
        have hqInvNonneg : (0 : Real) ≤ (q : Real)⁻¹ := inv_nonneg.mpr hqNonneg
        have hlastNonneg : (0 : Real) ≤
            (q : Real) * (t : Real) ^ (-(k : Real)) :=
          mul_nonneg hqNonneg
            (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le t) _)
        linarith
      have hrootLower : (t : Real)⁻¹ ≤
          weylRationalFactor k t q ^ ((K : Real))⁻¹ := by
        have hInvRoot : (t : Real)⁻¹ ≤
            ((t : Real)⁻¹) ^ ((K : Real))⁻¹ := by
          calc
            (t : Real)⁻¹ = (t : Real) ^ (-1 : Real) :=
              (Real.rpow_neg_one _).symm
            _ ≤ (t : Real) ^ ((-1 : Real) * (K : Real)⁻¹) := by
              apply Real.rpow_le_rpow_of_exponent_le htOne
              have hKOneNat : 1 ≤ K := by
                dsimp only [K, weylDifferencingPower]
                exact one_le_pow₀ (by norm_num)
              have hKOne : (1 : Real) ≤ K := by exact_mod_cast hKOneNat
              have hKinv : (K : Real)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hKOne
              linarith
            _ = ((t : Real)⁻¹) ^ ((K : Real))⁻¹ := by
              calc
                (t : Real) ^ ((-1 : Real) * (K : Real)⁻¹) =
                    ((t : Real) ^ (-1 : Real)) ^ ((K : Real))⁻¹ :=
                  Real.rpow_mul (by positivity) _ _
                _ = ((t : Real)⁻¹) ^ ((K : Real))⁻¹ := by
                  rw [Real.rpow_neg_one]
        exact hInvRoot.trans (Real.rpow_le_rpow (by positivity) hBinv (by positivity))
      have hCbig : (t : Real) ≤ C := by
        have htTReal : (t : Real) ≤ T := by exact_mod_cast htT.le
        have hrootNonneg : 0 ≤ Aeps ^ ((K : Real)⁻¹) := by positivity
        dsimp only [C]
        linarith
      calc
        ‖weylSum alpha k t‖ ≤ t := weylSum_norm_le alpha k t
        _ ≤ C * ((t : Real) ^ (1 + epsilon) * (t : Real)⁻¹) := by
          have hpow : 1 ≤ (t : Real) ^ (1 + epsilon) * (t : Real)⁻¹ := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add (by positivity)]
            exact Real.one_le_rpow htOne (by linarith)
          exact hCbig.trans (le_mul_of_one_le_right hC hpow)
        _ ≤ C * (t : Real) ^ (1 + epsilon) *
            weylRationalFactor k t q ^ ((K : Real))⁻¹ := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hrootLower
              (mul_nonneg hC (by positivity : 0 ≤ (t : Real) ^ (1 + epsilon)))
        _ = C * (t : Real) ^ (1 + epsilon) *
            weylRationalFactor k t q ^
              ((2 : Real) ^ (k - 1))⁻¹ := by rw [hrootExp]

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

private lemma nat_le_cube {k : Nat} (hk : 1 ≤ k) : k ≤ k ^ 3 := by
  calc
    k = k * 1 := by simp
    _ ≤ k * k ^ 2 := Nat.mul_le_mul_left k (one_le_pow₀ hk)
    _ = k ^ 3 := by ring

private lemma eight_le_cube {k : Nat} (hk : 2 ≤ k) : 8 ≤ k ^ 3 := by
  have hpow := Nat.pow_le_pow_left hk 3
  norm_num at hpow
  exact hpow

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
    _ ≤ 2 ^ (8 * k ^ 3) := by
      exact Nat.pow_le_pow_right (by norm_num) hexp

private lemma weylRaisedCoefficientNat_le {k : Nat} (hk : 2 ≤ k) :
    weylRaisedCoefficientNat k ≤ 2 ^ (2 ^ (20 * k ^ 3)) := by
  let m := weylDivisorParameter k
  let H := 2 ^ (16 * k ^ 3)
  have hm : m = 8 * k ^ 3 := rfl
  have hmpos : 1 ≤ m := by
    dsimp only [m, weylDivisorParameter]
    apply Nat.one_le_iff_ne_zero.mpr
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by omega))
  have hkOne : 1 ≤ k := hk.trans' (by norm_num)
  have hkCube : k ≤ k ^ 3 := nat_le_cube hkOne
  have hcubeEight : 8 ≤ k ^ 3 := eight_le_cube hk
  have hpoly : m * (k - 1) ≤ 2 ^ m := by
    rw [hm]
    have hcore : k ^ 3 * (k - 1) ≤ k ^ 4 := by
      rw [pow_succ]
      exact Nat.mul_le_mul_left _ (Nat.sub_le k 1)
    calc
      (8 * k ^ 3) * (k - 1) = 8 * (k ^ 3 * (k - 1)) := by ring
      _ ≤ 8 * k ^ 4 := Nat.mul_le_mul_left 8 hcore
      _ ≤ 2 ^ (8 * k ^ 3) :=
        eight_mul_pow_four_le_two_pow_eight_mul_cube (by omega : 1 ≤ k)
  have hExp : m * (k - 1) * 2 ^ m ≤ H := by
    calc
      m * (k - 1) * 2 ^ m ≤ 2 ^ m * 2 ^ m :=
        Nat.mul_le_mul_right _ hpoly
      _ = 2 ^ (16 * k ^ 3) := by
        rw [← pow_add, hm]
        congr 1
        ring
      _ = H := rfl
  have hmBase : m ≤ 2 ^ m := by
    exact (Nat.le_succ m).trans (nat_succ_le_two_pow m)
  have hmPower : m ^ ((k - 1) * 2 ^ m) ≤ 2 ^ H := by
    calc
      m ^ ((k - 1) * 2 ^ m) ≤
          (2 ^ m) ^ ((k - 1) * 2 ^ m) :=
        Nat.pow_le_pow_left hmBase _
      _ = 2 ^ (m * ((k - 1) * 2 ^ m)) :=
        (pow_mul 2 m ((k - 1) * 2 ^ m)).symm
      _ ≤ 2 ^ H := by
        apply Nat.pow_le_pow_right (by norm_num)
        simpa [mul_assoc] using hExp
  have hKexp : weylDifferencingPower k + 2 * k + 12 ≤ H := by
    have hkEightCube : k ≤ 8 * k ^ 3 :=
      hkCube.trans (by omega)
    have hlinExp : 2 * k + 12 ≤ 8 * k ^ 3 - 1 := by
      have htwo : 2 * k ≤ 2 * k ^ 3 := Nat.mul_le_mul_left 2 hkCube
      have hthirteen : 13 ≤ 6 * k ^ 3 := by omega
      have hsum : 2 * k + 13 ≤ 8 * k ^ 3 := by
        calc
          2 * k + 13 ≤ 2 * k ^ 3 + 6 * k ^ 3 :=
            Nat.add_le_add htwo hthirteen
          _ = 8 * k ^ 3 := by ring
      omega
    have hKsmall : weylDifferencingPower k ≤ 2 ^ (8 * k ^ 3 - 1) := by
      unfold weylDifferencingPower
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    have hlin : 2 * k + 12 ≤ 2 ^ (8 * k ^ 3 - 1) := by
      calc
        2 * k + 12 ≤ 2 * k + 12 + 1 := Nat.le_succ _
        _ ≤ 2 ^ (2 * k + 12) := nat_succ_le_two_pow (2 * k + 12)
        _ ≤ 2 ^ (8 * k ^ 3 - 1) := by
          exact Nat.pow_le_pow_right (by norm_num) hlinExp
    calc
      weylDifferencingPower k + 2 * k + 12 ≤
          2 ^ (8 * k ^ 3 - 1) + 2 ^ (8 * k ^ 3 - 1) :=
        by simpa only [Nat.add_assoc] using Nat.add_le_add hKsmall hlin
      _ = 2 ^ (8 * k ^ 3) := by
        have : 0 < 8 * k ^ 3 := by positivity
        rw [← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 8 * k ^ 3)]
      _ ≤ H := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
  have htwo : 2 ^ (weylDifferencingPower k + 2 * k + 12) ≤ 2 ^ H :=
    Nat.pow_le_pow_right (by norm_num) hKexp
  have hfac : Nat.factorial k ≤ 2 ^ H := by
    calc
      Nat.factorial k ≤ k ^ k := Nat.factorial_le_pow k
      _ ≤ (2 ^ k) ^ k := by
        apply Nat.pow_le_pow_left
        exact (Nat.le_succ k).trans (nat_succ_le_two_pow k)
      _ = 2 ^ (k ^ 2) := by
        calc
          (2 ^ k) ^ k = 2 ^ (k * k) := (pow_mul 2 k k).symm
          _ = 2 ^ (k ^ 2) := by rw [pow_two]
      _ ≤ 2 ^ H := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : k ^ 2 ≤ 2 ^ (2 * k) := by
          calc
            k ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left
              ((Nat.le_succ k).trans (nat_succ_le_two_pow k)) 2
            _ = 2 ^ (2 * k) := by
              calc
                (2 ^ k) ^ 2 = 2 ^ (k * 2) := (pow_mul 2 k 2).symm
                _ = 2 ^ (2 * k) := by rw [Nat.mul_comm]
        have htwoK : 2 * k ≤ 16 * k ^ 3 := by
          calc
            2 * k ≤ 2 * k ^ 3 := Nat.mul_le_mul_left 2 hkCube
            _ ≤ 16 * k ^ 3 := Nat.mul_le_mul_right (k ^ 3) (by norm_num)
        exact this.trans (by
          simpa only [H] using Nat.pow_le_pow_right (by norm_num) htwoK)
  have hkSucc : k + 1 ≤ 2 ^ H := by
    have hkH : k ≤ H := by
      calc
        k ≤ 16 * k ^ 3 + 1 := by
          exact hkCube.trans (by omega)
        _ ≤ 2 ^ (16 * k ^ 3) := nat_succ_le_two_pow (16 * k ^ 3)
        _ = H := rfl
    exact (nat_succ_le_two_pow k).trans
      (Nat.pow_le_pow_right (by norm_num) hkH)
  unfold weylRaisedCoefficientNat
  calc
    2 ^ (weylDifferencingPower k + 2 * k + 12) * Nat.factorial k *
          m ^ ((k - 1) * 2 ^ m) * (k + 1) ≤
        (2 ^ H) * (2 ^ H) * (2 ^ H) * (2 ^ H) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul htwo hfac) hmPower) hkSucc
    _ = 2 ^ (4 * H) := by
      calc
        (2 ^ H) * (2 ^ H) * (2 ^ H) * (2 ^ H) = (2 ^ H) ^ 4 := by ring
        _ = 2 ^ (H * 4) := (pow_mul 2 H 4).symm
        _ = 2 ^ (4 * H) := by rw [Nat.mul_comm]
    _ ≤ 2 ^ (2 ^ (20 * k ^ 3)) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hinner : 16 * k ^ 3 + 2 ≤ 20 * k ^ 3 := by omega
      calc
        4 * H = 2 ^ (16 * k ^ 3 + 2) := by
          dsimp only [H]
          calc
            4 * 2 ^ (16 * k ^ 3) =
                2 ^ 2 * 2 ^ (16 * k ^ 3) := by norm_num
            _ = 2 ^ (2 + 16 * k ^ 3) := by rw [pow_add]
            _ = 2 ^ (16 * k ^ 3 + 2) := by rw [Nat.add_comm]
        _ ≤ 2 ^ (20 * k ^ 3) := Nat.pow_le_pow_right (by norm_num) hinner

private lemma threshold_root_dominates {k t : Nat} (hk : 2 ≤ k)
    (ht : 2 ^ (2 ^ (40 * k ^ 3)) ≤ t) :
    (2 : Real) ^ (2 ^ (20 * k ^ 3)) ≤
      (t : Real) ^ ((32 * (k : Real))⁻¹) := by
  let G := 2 ^ (20 * k ^ 3)
  let H := 2 ^ (40 * k ^ 3)
  have hkpos : (0 : Real) < k := by positivity
  have hfactor : 32 * k ≤ G := by
    have hexp : 32 * k ≤ 20 * k ^ 3 :=
      thirty_two_mul_le_twenty_mul_cube hk
    calc
      32 * k ≤ 32 * k + 1 := Nat.le_succ _
      _ ≤ 2 ^ (32 * k) := nat_succ_le_two_pow (32 * k)
      _ ≤ G := by
        exact Nat.pow_le_pow_right (by norm_num) hexp
  have hGH : 32 * k * G ≤ H := by
    calc
      32 * k * G ≤ G * G := Nat.mul_le_mul_right G hfactor
      _ = H := by
        dsimp only [G, H]
        rw [← pow_add]
        congr 1
        ring
  have hbase : ((2 ^ H : Nat) : Real) ≤ t := by
    dsimp only [H]
    exact_mod_cast ht
  calc
    (2 : Real) ^ G ≤
        ((2 : Real) ^ H) ^ ((32 * (k : Real))⁻¹) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_natCast_mul (by norm_num : (0 : Real) ≤ 2)]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [mul_comm (H : Real) ((32 * (k : Real))⁻¹)]
      rw [le_inv_mul_iff₀ (mul_pos (by norm_num) hkpos)]
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
  let G := 2 ^ (20 * k ^ 3)
  let delta : Real := (32 * (k : Real))⁻¹
  let R : Real := (t : Real) ^ delta
  have hkpos : (0 : Real) < k := by positivity
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have htOneNat : 1 ≤ t := by
    exact (show 1 ≤ 2 ^ (2 ^ (40 * k ^ 3)) by
      exact one_le_pow₀ (by norm_num)).trans ht
  have htOne : (1 : Real) ≤ t := by exact_mod_cast htOneNat
  have hR : (2 : Real) ^ G ≤ R := by
    exact threshold_root_dominates hk ht
  have hcoeff : weylRaisedCoefficient k ≤ R := by
    calc
      weylRaisedCoefficient k = (weylRaisedCoefficientNat k : Real) :=
        weylRaisedCoefficient_eq_natCast k
      _ ≤ ((2 ^ G : Nat) : Real) := by
        exact_mod_cast weylRaisedCoefficientNat_le hk
      _ = (2 : Real) ^ G := by push_cast; rfl
      _ ≤ R := hR
  have hlinearNat : 1 + 32 * k ≤ 2 ^ G := by
    have hfactor : 32 * k ≤ G := by
      have hexp : 32 * k ≤ 20 * k ^ 3 :=
        thirty_two_mul_le_twenty_mul_cube hk
      calc
        32 * k ≤ 32 * k + 1 := Nat.le_succ _
        _ ≤ 2 ^ (32 * k) := nat_succ_le_two_pow (32 * k)
        _ ≤ G := by
          exact Nat.pow_le_pow_right (by norm_num) hexp
    calc
      1 + 32 * k ≤ G + 1 := by omega
      _ ≤ 2 ^ G := nat_succ_le_two_pow G
  have hlinear : (1 : Real) + 32 * k ≤ R := by
    calc
      (1 : Real) + 32 * k ≤ ((2 ^ G : Nat) : Real) := by
        exact_mod_cast hlinearNat
      _ = (2 : Real) ^ G := by push_cast; rfl
      _ ≤ R := hR
  have hlog : 1 + Real.log t ≤ ((1 : Real) + 32 * k) * R := by
    have hlogPow := Real.log_natCast_le_rpow_div t hdelta
    have hdeltaInv : delta⁻¹ = 32 * (k : Real) := by
      dsimp only [delta]
      rw [inv_inv]
    rw [div_eq_mul_inv, hdeltaInv] at hlogPow
    dsimp only [R]
    have hROne : 1 ≤ (t : Real) ^ delta := Real.one_le_rpow htOne hdelta.le
    nlinarith [mul_nonneg (by positivity : (0 : Real) ≤ 32 * k)
      (by positivity : 0 ≤ (t : Real) ^ delta)]
  have hproduct : weylRaisedCoefficient k * (1 + Real.log t) ≤ R ^ 3 := by
    have hlogNonneg : 0 ≤ 1 + Real.log t := by
      linarith [Real.log_nonneg htOne]
    have hRNonneg : 0 ≤ R := by dsimp only [R]; positivity
    have hfirst : weylRaisedCoefficient k * (1 + Real.log t) ≤
        R * (((1 : Real) + 32 * k) * R) :=
      mul_le_mul hcoeff hlog hlogNonneg hRNonneg
    have hsecond : ((1 : Real) + 32 * k) * R ≤ R * R :=
      mul_le_mul_of_nonneg_right hlinear hRNonneg
    calc
      _ ≤ R * (((1 : Real) + 32 * k) * R) := hfirst
      _ ≤ R * (R * R) := mul_le_mul_of_nonneg_left hsecond hRNonneg
      _ = R ^ 3 := by ring
  have hRpow : R ^ 3 ≤ (t : Real) ^ ((8 * (k : Real))⁻¹) := by
    dsimp only [R, delta]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    apply Real.rpow_le_rpow_of_exponent_le htOne
    field_simp [ne_of_gt hkpos]
    <;> ring_nf
    <;> norm_num
  calc
    weylRaisedCoefficient k * (1 + Real.log t) ≤ R ^ 3 := hproduct
    _ ≤ (t : Real) ^ ((8 * (k : Real))⁻¹) := hRpow
    _ ≤ (1000 : Real) ^ weylDifferencingPower k *
        (t : Real) ^ ((8 * (k : Real))⁻¹) := by
      exact le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by norm_num : (1 : Real) ≤ 1000))

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
  have htOneNat : 1 ≤ t := by
    exact (show 1 ≤ repairedWeylThreshold k by
      unfold repairedWeylThreshold
      exact one_le_pow₀ (by norm_num : 1 ≤ (2 : Nat))).trans ht
  have htOne : (1 : Real) ≤ t := by exact_mod_cast htOneNat
  by_cases hkOne : k = 1
  ·
    have hbasic := weyl_degree_one_bound t a q alpha hq haq halpha
    have hpow : (t : Real) ≤ 1000 * (t : Real) ^ (1 + (4 : Real)⁻¹) := by
      have hmono : (t : Real) ≤ (t : Real) ^ (1 + (4 : Real)⁻¹) := by
        calc
          (t : Real) = (t : Real) ^ (1 : Real) := by simp
          _ ≤ (t : Real) ^ (1 + (4 : Real)⁻¹) :=
            Real.rpow_le_rpow_of_exponent_le
              (x := (t : Real)) (y := (1 : Real))
              (z := 1 + (4 : Real)⁻¹) htOne (by norm_num)
      exact hmono.trans
        (le_mul_of_one_le_left (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le t) _)
          (by norm_num : (1 : Real) ≤ 1000))
    have hmul : (t : Real) * weylRationalFactor 1 t q ≤
        1000 * (t : Real) ^ (1 + (4 : Real)⁻¹) *
          weylRationalFactor 1 t q :=
      mul_le_mul_of_nonneg_right hpow
        (weylRationalFactor_nonneg (k := 1) (t := t) hq)
    calc
      ‖weylSum alpha k t‖ = ‖weylSum alpha 1 t‖ := by rw [hkOne]
      _ ≤ (t : Real) * weylRationalFactor 1 t q := hbasic
      _ ≤ 1000 * (t : Real) ^ (1 + (4 : Real)⁻¹) *
          weylRationalFactor 1 t q := hmul
      _ = 1000 * (t : Real) ^
            (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) *
          (weylRationalFactor k t q ^
            ((2 : Real) ^ (k - 1))⁻¹) := by
        rw [hkOne]
        norm_num only [Nat.cast_one, one_mul, one_add_one_eq_two, pow_two,
          Nat.sub_self, pow_zero, inv_one, Real.rpow_one]
  · have hkTwo : 2 ≤ k := by omega
    have htTwo : 2 ≤ t := by
      exact hkTwo.trans (repairedWeylThreshold_ge_self hk |>.trans ht)
    have hkt : k ≤ t := repairedWeylThreshold_ge_self hk |>.trans ht
    let K := weylDifferencingPower k
    let m := weylDivisorParameter k
    let eta : Real := (((k - 1 : Nat) : Real) ^ 2) / m
    let B := weylRationalFactor k t q
    have hKposNat : 0 < K := by
      dsimp only [K, weylDifferencingPower]
      exact pow_pos (by norm_num : 0 < (2 : Nat)) _
    have hKpos : (0 : Real) < K := by exact_mod_cast hKposNat
    have hm : 1 ≤ m := by
      dsimp only [m, weylDivisorParameter]
      apply Nat.one_le_iff_ne_zero.mpr
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by omega))
    have heta : eta ≤ (8 * (k : Real))⁻¹ := by
      exact weyl_divisor_exponent_le hk
    have hB : 0 ≤ B := weylRationalFactor_nonneg hq
    have hraised := weyl_raised_estimate
      (alpha := alpha) (k := k) (t := t) (m := m)
      hkTwo htTwo hkt hm a q hq haq halpha
    have habsorb := weyl_coefficient_log_absorbed hkTwo ht
    have hexponent : (K : Real) + eta + (8 * (k : Real))⁻¹ ≤
        K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by
      have hKform : (K : Real) = (2 : Real) ^ (k - 1) := by
        dsimp only [K, weylDifferencingPower]
        push_cast <;> rfl
      rw [hKform]
      have hkReal : (0 : Real) < k := by positivity
      have hpow : (2 : Real) ^ (k + 1) = 4 * (2 : Real) ^ (k - 1) := by
        have : k + 1 = (k - 1) + 2 := by omega
        rw [this, pow_add]
        norm_num
        <;> ring
      have hbonus : (2 : Real) ^ (k - 1) *
          ((k : Real) * (2 : Real) ^ (k + 1))⁻¹ =
          (4 * (k : Real))⁻¹ := by
        rw [hpow]
        field_simp [ne_of_gt hkReal]
        <;> ring
      rw [mul_add, mul_one, hbonus]
      calc
        (2 : Real) ^ (k - 1) + eta + (8 * (k : Real))⁻¹ ≤
            (2 : Real) ^ (k - 1) + (8 * (k : Real))⁻¹ +
              (8 * (k : Real))⁻¹ := by
          linarith [heta]
        _ = (2 : Real) ^ (k - 1) + (4 * (k : Real))⁻¹ := by
          field_simp [ne_of_gt hkReal]
          <;> ring
    have hraised' : ‖weylSum alpha k t‖ ^ K ≤
        (1000 : Real) ^ K *
          (t : Real) ^
            (K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * B := by
      calc
        _ ≤ weylRaisedCoefficient k *
            (t : Real) ^ ((K : Real) + eta) * B * (1 + Real.log t) := by
          simpa only [weylRaisedCoefficient, K, m, eta, B] using hraised
        _ = (weylRaisedCoefficient k * (1 + Real.log t)) *
            (t : Real) ^ ((K : Real) + eta) * B := by ring
        _ ≤ ((1000 : Real) ^ K *
              (t : Real) ^ ((8 * (k : Real))⁻¹)) *
            (t : Real) ^ ((K : Real) + eta) * B := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right habsorb (by positivity)) hB
        _ = (1000 : Real) ^ K *
            ((t : Real) ^ ((K : Real) + eta) *
              (t : Real) ^ ((8 * (k : Real))⁻¹)) * B := by ring
        _ = (1000 : Real) ^ K *
            (t : Real) ^
              ((K : Real) + eta + (8 * (k : Real))⁻¹) * B := by
          rw [← Real.rpow_add (by positivity)]
        _ ≤ (1000 : Real) ^ K *
            (t : Real) ^
              (K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * B := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le htOne hexponent)
              (by positivity)) hB
    have hroot : ‖weylSum alpha k t‖ ≤
        ((1000 : Real) ^ K *
          (t : Real) ^
            (K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * B) ^
              ((K : Real))⁻¹ :=
      (Real.le_rpow_inv_iff_of_pos
        (x := ‖weylSum alpha k t‖)
        (y := (1000 : Real) ^ K *
          (t : Real) ^
            (K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * B)
        (z := (K : Real)) (norm_nonneg _) (by positivity) hKpos).2 (by
          simpa only [Real.rpow_natCast] using hraised')
    have hKcancel : (K : Real) * (K : Real)⁻¹ = 1 :=
      mul_inv_cancel₀ hKpos.ne'
    have hconstRoot :
        (((1000 : Real) ^ K) ^ ((K : Real))⁻¹) = 1000 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hKcancel,
        Real.rpow_one]
    have htRoot :
        (((t : Real) ^
            (K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹))) ^
              ((K : Real))⁻¹) =
          (t : Real) ^
            (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      calc
        (K : Real) *
              (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) *
            (K : Real)⁻¹ =
            ((K : Real) * (K : Real)⁻¹) *
              (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by ring
        _ = 1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹ := by
          rw [hKcancel, one_mul]
    have hKform : (K : Real) = (2 : Real) ^ (k - 1) := by
      dsimp only [K, weylDifferencingPower]
      push_cast <;> rfl
    calc
      ‖weylSum alpha k t‖ ≤
          ((1000 : Real) ^ K *
            (t : Real) ^
              (K * (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * B) ^
                ((K : Real))⁻¹ := hroot
      _ = 1000 * (t : Real) ^
          (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) *
            B ^ ((K : Real))⁻¹ := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hconstRoot, htRoot]
      _ = 1000 * (t : Real) ^
          (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) *
            B ^ ((2 : Real) ^ (k - 1))⁻¹ := by rw [hKform]

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
