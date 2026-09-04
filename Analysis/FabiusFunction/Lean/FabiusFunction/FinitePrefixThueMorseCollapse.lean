import FabiusFunction.FinitePrefixAppellRecovery
import FabiusFunction.ThueMorseMoments
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Complete Thue--Morse responses of finite dyadic Appell prefixes

The finite-prefix Appell polynomials are tailored inverses of successive
uniform averages.  A signed endpoint difference cancels one uniform factor,
so the complete depth-`N` Thue--Morse block cancels all `N` factors and leaves
the `N`-th Appell derivative of a monomial.  This gives the two collapses
printed in the inverse-frontier manuscript:

* the uncentered Kabaya--Iri prefix has response
  `(-1)^N 2^{-C(N+1,2)} n.descFactorial N x^(n-N)`;
* the centered Rvachev prefix has response
  `2^{-C(N,2)} n.descFactorial N x^(n-N)`.

The proofs are coefficientwise.  The only special-function input is the
ordinary Bernoulli difference equation, used to cancel one uniform digit.
The dyadic induction itself is the even/odd splitting of a complete
Thue--Morse block.  In particular, no analytic generating function or
convergence argument is involved.

The primary statements are total at depth zero.  The centered theorem also
has a successor-indexed form whose grid is literally the manuscript's
`x + s_N - k / 2^(N-1)`, avoiding truncated natural subtraction.

## Main declarations

* `Appell.sum_thueMorseSign_mul_eval_poly` gives the complete response of an
  arbitrary rational Appell polynomial in terms of the signed power moments.
* `sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat` is the
  uncentered finite-prefix collapse, including depth zero.
* `sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat` is the
  centered collapse on a total common-denominator grid.
* the `_of_lt` and `_self` corollaries record Prouhet cancellation and its
  first nonzero constant.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Polynomial

noncomputable section

namespace Appell

/-- Translation of an Appell polynomial, evaluated coefficientwise. -/
private theorem eval_poly_add (b : ℕ → ℚ) (n : ℕ) (x y : ℚ) :
    (poly b n).eval (x + y) =
      ∑ r ∈ range (n + 1),
        (n.choose r : ℚ) * y ^ r * (poly b (n - r)).eval x := by
  have h := congrArg (Polynomial.eval y) (poly_translate b x n)
  rw [eval_poly_eq_sum] at h
  simpa only [translate, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, add_comm, mul_comm, mul_assoc]
    using h.symm

/-- **Complete Thue--Morse response of an arbitrary Appell polynomial.**
Translation expands an Appell polynomial against its lower-index companions;
therefore a complete signed dyadic block acts diagonally through the signed
power moments `thueMorsePowerSum`.  No normalization of `b` is required. -/
theorem sum_thueMorseSign_mul_eval_poly
    (b : ℕ → ℚ) (N n : ℕ) (x h : ℚ) :
    (∑ k : Fin (2 ^ N), (Fabius.thueMorseSign k.val : ℚ) *
        (poly b n).eval (x + (k.val : ℚ) * h)) =
      ∑ r ∈ range (n + 1),
        (n.choose r : ℚ) * h ^ r *
          Fabius.thueMorsePowerSum N r * (poly b (n - r)).eval x := by
  simp_rw [eval_poly_add]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [Fabius.thueMorsePowerSum]
  calc
    (∑ k : Fin (2 ^ N),
        (Fabius.thueMorseSign k.val : ℚ) *
          ((n.choose r : ℚ) * ((k.val : ℚ) * h) ^ r *
            (poly b (n - r)).eval x)) =
        ∑ k : Fin (2 ^ N),
          ((n.choose r : ℚ) * h ^ r) *
            ((Fabius.thueMorseSign k.val : ℚ) * (k.val : ℚ) ^ r) *
              (poly b (n - r)).eval x := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [mul_pow]
      ring
    _ = (n.choose r : ℚ) * h ^ r *
          (∑ k : Fin (2 ^ N),
            (Fabius.thueMorseSign k.val : ℚ) * (k.val : ℚ) ^ r) *
            (poly b (n - r)).eval x := by
      rw [Finset.mul_sum, Finset.sum_mul]

end Appell

namespace Fabius

/-! ## One uniform digit -/

private theorem reciprocal_unitSeq_rat :
    Bell.reciprocal (Bell.unitSeq ℚ) = Bell.unitSeq ℚ := by
  symm
  apply Bell.eq_reciprocal_of_binomialConv
  · rfl
  · exact Bell.binomialConv_unitSeq_right (Bell.unitSeq ℚ)

private theorem eval_poly_reciprocal_unitSeq_rat (n : ℕ) (x : ℚ) :
    (Appell.poly (Bell.reciprocal (Bell.unitSeq ℚ)) n).eval x = x ^ n := by
  rw [reciprocal_unitSeq_rat, Appell.eval_poly]
  exact congrFun
    (Bell.binomialConv_unitSeq_right (fun k : ℕ ↦ x ^ k)) n

private theorem appell_poly_bernoulli (n : ℕ) :
    Appell.poly (_root_.bernoulli : ℕ → ℚ) n = Polynomial.bernoulli n := by
  ext j
  rw [Appell.coeff_poly, Polynomial.coeff_bernoulli]
  split_ifs <;> ring

private theorem binomialConv_unitUniformRawMomentRat_bernoulli :
    Bell.binomialConv unitUniformRawMomentRat
        (_root_.bernoulli : ℕ → ℚ) =
      Bell.unitSeq ℚ := by
  funext n
  cases n with
  | zero => norm_num [Bell.binomialConv, unitUniformRawMomentRat, Bell.unitSeq]
  | succ n =>
      rw [Bell.binomialConv_eq_sum_range]
      change
        (∑ k ∈ range (n + 2),
            ((n + 1).choose k : ℚ) *
              (unitUniformRawMomentRat k * _root_.bernoulli (n + 1 - k))) = 0
      calc
        (∑ k ∈ range (n + 2),
            ((n + 1).choose k : ℚ) *
              (unitUniformRawMomentRat k * _root_.bernoulli (n + 1 - k))) =
            ∑ k ∈ range (n + 2),
              ((n + 2).choose k : ℚ) * _root_.bernoulli k / (n + 2 : ℚ) := by
          rw [← Finset.sum_range_reflect
            (fun k ↦ ((n + 1).choose k : ℚ) *
              (unitUniformRawMomentRat k * _root_.bernoulli (n + 1 - k)))
            (n + 2)]
          apply Finset.sum_congr rfl
          intro k hk
          have hkn : k ≤ n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hk)
          rw [show n + 2 - 1 - k = n + 1 - k by omega,
            Nat.choose_symm hkn, Nat.sub_sub_self hkn,
            unitUniformRawMomentRat]
          have hnat := Nat.choose_mul_succ_eq (n + 1) k
          have hsub : n + 1 - k + 1 = n + 2 - k := by omega
          rw [hsub]
          have hrat :
              (((n + 1).choose k : ℕ) : ℚ) *
                  ((n + 2 : ℕ) : ℚ) =
                (((n + 2).choose k : ℕ) : ℚ) *
                  ((n + 2 - k : ℕ) : ℚ) := by
            exact_mod_cast hnat
          have hrat' :
              (((n + 1).choose k : ℕ) : ℚ) * ((n : ℚ) + 2) =
                (((n + 2).choose k : ℕ) : ℚ) *
                  ((n + 2 - k : ℕ) : ℚ) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using hrat
          have hden1 : ((n + 2 : ℕ) : ℚ) ≠ 0 := by positivity
          have hden2 : ((n + 2 - k : ℕ) : ℚ) ≠ 0 := by
            have hpos : 0 < n + 2 - k := Nat.sub_pos_of_lt (by omega)
            exact_mod_cast hpos.ne'
          field_simp [hden1, hden2]
          linear_combination hrat' * _root_.bernoulli k
        _ = 0 := by
          rw [← Finset.sum_div, _root_.sum_bernoulli]
          simp

private theorem reciprocal_dilate_unitUniformRawMomentRat (a : ℚ) :
    Bell.reciprocal (Appell.dilate a unitUniformRawMomentRat) =
      Appell.dilate a (_root_.bernoulli : ℕ → ℚ) := by
  symm
  apply Bell.eq_reciprocal_of_binomialConv
  · simp [Appell.dilate, unitUniformRawMomentRat]
  · rw [Appell.binomialConv_dilate,
      binomialConv_unitUniformRawMomentRat_bernoulli]
    funext n
    cases n <;> simp [Appell.dilate, Bell.unitSeq]

private theorem binomialConv_four_swap
    (a b c d : ℕ → ℚ) :
    Bell.binomialConv (Bell.binomialConv a b) (Bell.binomialConv c d) =
      Bell.binomialConv (Bell.binomialConv a c) (Bell.binomialConv b d) := by
  calc
    Bell.binomialConv (Bell.binomialConv a b) (Bell.binomialConv c d) =
        Bell.binomialConv a
          (Bell.binomialConv b (Bell.binomialConv c d)) :=
      Bell.binomialConv_assoc _ _ _
    _ = Bell.binomialConv a
          (Bell.binomialConv c (Bell.binomialConv b d)) := by
      rw [← Bell.binomialConv_assoc b c d,
        Bell.binomialConv_comm b c, Bell.binomialConv_assoc]
    _ = Bell.binomialConv (Bell.binomialConv a c)
          (Bell.binomialConv b d) :=
      (Bell.binomialConv_assoc _ _ _).symm

private theorem reciprocal_uncenteredDyadicPrefixMomentRat_succ (N : ℕ) :
    Bell.reciprocal (uncenteredDyadicPrefixMomentRat (N + 1)) =
      Bell.binomialConv
        (Bell.reciprocal (uncenteredDyadicPrefixMomentRat N))
        (Appell.dilate (dyadicPrefixScaleRat (N + 1))
          (_root_.bernoulli : ℕ → ℚ)) := by
  symm
  apply Bell.eq_reciprocal_of_binomialConv
  · exact uncenteredDyadicPrefixMomentRat_zero (N + 1)
  · change Bell.binomialConv
        (Bell.binomialConv (uncenteredDyadicPrefixMomentRat N)
          (Appell.dilate (dyadicPrefixScaleRat (N + 1))
            unitUniformRawMomentRat))
        (Bell.binomialConv
          (Bell.reciprocal (uncenteredDyadicPrefixMomentRat N))
          (Appell.dilate (dyadicPrefixScaleRat (N + 1))
            (_root_.bernoulli : ℕ → ℚ))) = Bell.unitSeq ℚ
    calc
      _ = Bell.binomialConv
            (Bell.binomialConv (uncenteredDyadicPrefixMomentRat N)
              (Bell.reciprocal (uncenteredDyadicPrefixMomentRat N)))
            (Bell.binomialConv
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                unitUniformRawMomentRat)
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                (_root_.bernoulli : ℕ → ℚ))) :=
          binomialConv_four_swap _ _ _ _
      _ = Bell.binomialConv (Bell.unitSeq ℚ)
            (Bell.binomialConv
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                unitUniformRawMomentRat)
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                (_root_.bernoulli : ℕ → ℚ))) := by
          rw [Bell.binomialConv_reciprocal _
            (uncenteredDyadicPrefixMomentRat_zero N)]
      _ = Bell.binomialConv
            (Appell.dilate (dyadicPrefixScaleRat (N + 1))
              unitUniformRawMomentRat)
            (Appell.dilate (dyadicPrefixScaleRat (N + 1))
              (_root_.bernoulli : ℕ → ℚ)) :=
          Bell.binomialConv_unitSeq_left _
      _ = Bell.binomialConv
            (Appell.dilate (dyadicPrefixScaleRat (N + 1))
              unitUniformRawMomentRat)
            (Bell.reciprocal
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                unitUniformRawMomentRat)) := by
          rw [reciprocal_dilate_unitUniformRawMomentRat]
      _ = Bell.unitSeq ℚ :=
          Bell.binomialConv_reciprocal _ (by
            simp [Appell.dilate, unitUniformRawMomentRat])

private theorem eval_poly_dilate_bernoulli
    (a : ℚ) (ha : a ≠ 0) (n : ℕ) (x : ℚ) :
    (Appell.poly (Appell.dilate a (_root_.bernoulli : ℕ → ℚ)) n).eval x =
      a ^ n * (Polynomial.bernoulli n).eval (x / a) := by
  have h := congrArg (Polynomial.eval (x / a))
    (Appell.poly_dilate_comp (_root_.bernoulli : ℕ → ℚ) a n)
  have hxa : a * (x / a) = x := by field_simp
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, hxa, appell_poly_bernoulli] using h

private theorem eval_poly_dilate_bernoulli_add_sub
    (a : ℚ) (ha : a ≠ 0) (n : ℕ) (x : ℚ) :
    (Appell.poly (Appell.dilate a (_root_.bernoulli : ℕ → ℚ)) n).eval (x + a) -
        (Appell.poly (Appell.dilate a (_root_.bernoulli : ℕ → ℚ)) n).eval x =
      a * (n : ℚ) * x ^ (n - 1) := by
  cases n with
  | zero => simp [Appell.poly_zero, Appell.dilate]
  | succ n =>
      rw [eval_poly_dilate_bernoulli a ha,
        eval_poly_dilate_bernoulli a ha]
      have harg : (x + a) / a = 1 + x / a := by
        field_simp
        ring
      rw [harg, Polynomial.bernoulli_eval_one_add]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      rw [pow_succ, div_pow]
      field_simp [ha]
      ring

private theorem eval_poly_eq_sum_rev
    (b : ℕ → ℚ) (n : ℕ) (x : ℚ) :
    (Appell.poly b n).eval x =
      ∑ r ∈ range (n + 1),
        (n.choose r : ℚ) * b r * x ^ (n - r) := by
  rw [Appell.eval_poly_eq_sum,
    ← Finset.sum_range_reflect
      (fun k ↦ (n.choose k : ℚ) * b (n - k) * x ^ k) (n + 1)]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm hrn, Nat.sub_sub_self hrn]

private theorem uncenteredPrefixAppell_eval_sub_add (N n : ℕ) (x : ℚ) :
    (uncenteredDyadicPrefixAppellPolynomialRat (N + 1) n).eval x -
        (uncenteredDyadicPrefixAppellPolynomialRat (N + 1) n).eval
          (x + dyadicPrefixScaleRat (N + 1)) =
      -(dyadicPrefixScaleRat (N + 1) * (n : ℚ) *
        (uncenteredDyadicPrefixAppellPolynomialRat N (n - 1)).eval x) := by
  let a : ℚ := dyadicPrefixScaleRat (N + 1)
  have ha : a ≠ 0 := by
    simp [a, dyadicPrefixScaleRat]
  cases n with
  | zero =>
      simp [uncenteredDyadicPrefixAppellPolynomialRat, Appell.poly_zero,
        Bell.reciprocal_zero]
  | succ n =>
      rw [uncenteredDyadicPrefixAppellPolynomialRat,
        reciprocal_uncenteredDyadicPrefixMomentRat_succ,
        Appell.poly_binomialConv]
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C]
      rw [← Finset.sum_sub_distrib, Finset.sum_range_succ]
      have hlast :
          ((n + 1).choose (n + 1) : ℚ) *
              Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) (n + 1) *
                (Appell.poly (Appell.dilate a
                  (_root_.bernoulli : ℕ → ℚ)) 0).eval x -
            ((n + 1).choose (n + 1) : ℚ) *
              Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) (n + 1) *
                (Appell.poly (Appell.dilate a
                  (_root_.bernoulli : ℕ → ℚ)) 0).eval (x + a) = 0 := by
        simp [Appell.poly_zero, Appell.dilate]
      simp only [Nat.sub_self]
      dsimp only [a] at hlast
      rw [hlast, add_zero]
      rw [show n + 1 - 1 = n by omega]
      suffices hmain :
          (∑ r ∈ range (n + 1), (
            ((n + 1).choose r : ℚ) *
                Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) r *
                  (Appell.poly (Appell.dilate a
                    (_root_.bernoulli : ℕ → ℚ)) (n + 1 - r)).eval x -
              ((n + 1).choose r : ℚ) *
                Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) r *
                  (Appell.poly (Appell.dilate a
                    (_root_.bernoulli : ℕ → ℚ)) (n + 1 - r)).eval (x + a))) =
            -(a * (n + 1 : ℚ) *
              (uncenteredDyadicPrefixAppellPolynomialRat N n).eval x) by
        simpa only [a, Nat.cast_add, Nat.cast_one] using hmain
      calc
        _ =
            ∑ r ∈ range (n + 1),
              -(a * (n + 1 : ℚ) *
                ((n.choose r : ℚ) *
                  Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) r *
                    x ^ (n - r))) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
          have hstep := eval_poly_dilate_bernoulli_add_sub a ha
            (n + 1 - r) x
          have hsub : n + 1 - r - 1 = n - r := by omega
          have hchoose := Nat.choose_mul_succ_eq n r
          have hchooseNat :
              (n + 1).choose r * (n + 1 - r) =
                (n + 1) * n.choose r := by
            calc
              (n + 1).choose r * (n + 1 - r) =
                  n.choose r * (n + 1) := hchoose.symm
              _ = (n + 1) * n.choose r := Nat.mul_comm _ _
          have hchooseQ :
              ((n + 1).choose r : ℚ) *
                  ((n + 1 - r : ℕ) : ℚ) =
                ((n + 1 : ℕ) : ℚ) * (n.choose r : ℚ) := by
            exact_mod_cast hchooseNat
          rw [hsub] at hstep
          calc
            _ = -(((n + 1).choose r : ℚ) *
                Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) r *
                  ((Appell.poly (Appell.dilate a
                    (_root_.bernoulli : ℕ → ℚ)) (n + 1 - r)).eval
                      (x + a) -
                    (Appell.poly (Appell.dilate a
                      (_root_.bernoulli : ℕ → ℚ)) (n + 1 - r)).eval
                        x)) := by ring
            _ = -(((n + 1).choose r : ℚ) *
                Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) r *
                  (a * ((n + 1 - r : ℕ) : ℚ) * x ^ (n - r))) := by
              rw [hstep]
            _ = -(a *
                (((n + 1).choose r : ℚ) *
                  ((n + 1 - r : ℕ) : ℚ)) *
                (Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) r *
                  x ^ (n - r))) := by ring
            _ = _ := by
              rw [hchooseQ]
              norm_num only [Nat.cast_add, Nat.cast_one]
              ring
        _ = -(a * (n + 1 : ℚ) *
              (uncenteredDyadicPrefixAppellPolynomialRat N n).eval x) := by
          rw [uncenteredDyadicPrefixAppellPolynomialRat,
            eval_poly_eq_sum_rev, Finset.mul_sum,
            ← Finset.sum_neg_distrib]

/-! ## Uncentered collapse -/

/-- **Uncentered Thue--Morse--Kabaya collapse.**  The complete depth-`N`
signed block applied to the depth-`N` prefix Appell polynomial is exactly the
`N`-th finite-difference monomial response.  The formula is total at `N = 0`;
when `n < N`, `Nat.descFactorial` makes the right side zero. -/
theorem sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat
    (N n : ℕ) (x : ℚ) :
    (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
        (uncenteredDyadicPrefixAppellPolynomialRat N n).eval
          (x + (k.val : ℚ) / (2 : ℚ) ^ N)) =
      (-1 : ℚ) ^ N * (1 / 2 : ℚ) ^ (N + 1).choose 2 *
        (n.descFactorial N : ℚ) * x ^ (n - N) := by
  induction N generalizing n x with
  | zero =>
      simpa [uncenteredDyadicPrefixAppellPolynomialRat,
        uncenteredDyadicPrefixMomentRat, dyadicPrefixMomentRat,
        thueMorseSign, binaryWeight] using
        (eval_poly_reciprocal_unitSeq_rat n x)
  | succ N ih =>
      have hcard : 2 ^ (N + 1) = 2 * 2 ^ N := by
        rw [pow_succ]
        omega
      rw [hcard]
      let f : ℕ → ℚ := fun k ↦
        (uncenteredDyadicPrefixAppellPolynomialRat (N + 1) n).eval
          (x + (k : ℚ) / (2 : ℚ) ^ (N + 1))
      change (∑ k : Fin (2 * 2 ^ N),
          (thueMorseSign k.val : ℚ) * f k.val) = _
      rw [thueMorse_sum_two_mul]
      have hpair (k : Fin (2 ^ N)) :
          f (2 * k.val) - f (2 * k.val + 1) =
            -(dyadicPrefixScaleRat (N + 1) * (n : ℚ) *
              (uncenteredDyadicPrefixAppellPolynomialRat N (n - 1)).eval
                (x + (k.val : ℚ) / (2 : ℚ) ^ N)) := by
        convert uncenteredPrefixAppell_eval_sub_add N n
          (x + (k.val : ℚ) / (2 : ℚ) ^ N) using 1
        simp [f, dyadicPrefixScaleRat, pow_succ]
        ring_nf
      have hfactor :
          (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
            -(dyadicPrefixScaleRat (N + 1) * (n : ℚ) *
              (uncenteredDyadicPrefixAppellPolynomialRat N (n - 1)).eval
                (x + (k.val : ℚ) / (2 : ℚ) ^ N))) =
            -(dyadicPrefixScaleRat (N + 1) * (n : ℚ)) *
              (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
                (uncenteredDyadicPrefixAppellPolynomialRat N (n - 1)).eval
                  (x + (k.val : ℚ) / (2 : ℚ) ^ N)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      simp_rw [hpair]
      rw [hfactor]
      cases n with
      | zero =>
          simp
      | succ n =>
          rw [show n + 1 - 1 = n by omega]
          rw [ih n]
          simp only [Nat.succ_sub_succ_eq_sub, Nat.cast_add, Nat.cast_one,
            Nat.succ_descFactorial_succ]
          have htri : (N + 2).choose 2 = (N + 1).choose 2 + (N + 1) := by
            rw [Nat.choose_succ_succ]
            simp [add_comm]
          rw [htri, pow_add, pow_succ]
          simp [dyadicPrefixScaleRat]
          ring

/-- Prouhet cancellation for the uncentered finite-prefix Appell polynomial
below the block depth. -/
theorem sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_of_lt
    (N n : ℕ) (hn : n < N) (x : ℚ) :
    (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
        (uncenteredDyadicPrefixAppellPolynomialRat N n).eval
          (x + (k.val : ℚ) / (2 : ℚ) ^ N)) = 0 := by
  rw [sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat,
    Nat.descFactorial_eq_zero_iff_lt.mpr hn, Nat.cast_zero, mul_zero, zero_mul]

/-- The first nonzero uncentered response is the manuscript's constant
`(-1)^N N! 2^{-N(N+1)/2}`. -/
theorem sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_self
    (N : ℕ) (x : ℚ) :
    (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
        (uncenteredDyadicPrefixAppellPolynomialRat N N).eval
          (x + (k.val : ℚ) / (2 : ℚ) ^ N)) =
      (-1 : ℚ) ^ N * (N.factorial : ℚ) *
        (1 / 2 : ℚ) ^ (N + 1).choose 2 := by
  rw [sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat,
    Nat.descFactorial_self, Nat.sub_self, pow_zero]
  ring

/-! ## Centered collapse -/

private theorem appell_poly_unitUniformRawMomentRat (n : ℕ) :
    C (n + 1 : ℚ) * Appell.poly unitUniformRawMomentRat n =
      (X + 1) ^ (n + 1) - X ^ (n + 1) := by
  ext j
  rw [coeff_C_mul, Appell.coeff_poly, coeff_sub,
    coeff_X_add_one_pow, coeff_X_pow]
  by_cases hj : j ≤ n
  · rw [if_pos hj, if_neg (by omega : j ≠ n + 1)]
    simp only [unitUniformRawMomentRat]
    have hnat := Nat.choose_mul_succ_eq n j
    have hsub : n + 1 - j = n - j + 1 := by omega
    have hchooseNat :
        (n + 1) * n.choose j =
          (n - j + 1) * (n + 1).choose j := by
      calc
        (n + 1) * n.choose j = n.choose j * (n + 1) :=
          Nat.mul_comm _ _
        _ = (n + 1).choose j * (n + 1 - j) := hnat
        _ = (n - j + 1) * (n + 1).choose j := by
          rw [hsub, Nat.mul_comm]
    have hchooseQ :
        ((n : ℚ) + 1) * (n.choose j : ℚ) =
          ((n - j + 1 : ℕ) : ℚ) * ((n + 1).choose j : ℚ) := by
      exact_mod_cast hchooseNat
    have hden : ((n - j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp [hden]
    simpa only [sub_zero] using hchooseQ
  · rw [if_neg hj]
    by_cases hjs : j = n + 1
    · subst j
      simp
    · have hjgt : n + 1 < j := by omega
      rw [Nat.choose_eq_zero_of_lt hjgt, if_neg hjs]
      simp

private theorem eval_appell_poly_unitUniformRawMomentRat (n : ℕ) (x : ℚ) :
    (Appell.poly unitUniformRawMomentRat n).eval x =
      ((x + 1) ^ (n + 1) - x ^ (n + 1)) / (n + 1 : ℚ) := by
  have h := congrArg (Polynomial.eval x)
    (appell_poly_unitUniformRawMomentRat n)
  have hden : (n + 1 : ℚ) ≠ 0 := by positivity
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] at h
  exact (eq_div_iff hden).2 (by simpa only [mul_comm] using h)

private theorem centeredUnitUniformRawMomentRat_eq_affine :
    centeredUnitUniformRawMomentRat =
      Appell.dilate 2
        (Appell.translate (-1 / 2 : ℚ) unitUniformRawMomentRat) := by
  funext n
  rw [Appell.dilate, Appell.translate,
    eval_appell_poly_unitUniformRawMomentRat]
  have hhalf : (-1 / 2 : ℚ) + 1 = 1 / 2 := by norm_num
  rw [hhalf]
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, hk⟩ := hn
    have hnform : n = 2 * k := by omega
    rw [hnform]
    rw [centeredUnitUniformRawMomentRat, if_pos (by exact ⟨k, by omega⟩)]
    have hneg : (-1 / 2 : ℚ) ^ (2 * k + 1) =
        -(1 / 2 : ℚ) ^ (2 * k + 1) := by
      rw [show (-1 / 2 : ℚ) = -(1 / 2) by ring, neg_pow]
      simp [pow_add, pow_mul]
    rw [hneg]
    field_simp
    have hhalfPow :
        (2 : ℚ) ^ (2 * k) * (1 / 2 : ℚ) ^ (2 * k + 1) = 1 / 2 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]
      norm_num
    push_cast
    linear_combination
      (-2 * (2 * (k : ℚ) + 1)) * hhalfPow
  · obtain ⟨k, hk⟩ := hn
    have hnform : n = 2 * k + 1 := by omega
    rw [hnform]
    rw [centeredUnitUniformRawMomentRat, if_neg (by
      exact Nat.not_even_iff_odd.mpr ⟨k, by omega⟩)]
    have hneg : (-1 / 2 : ℚ) ^ (2 * k + 1 + 1) =
        (1 / 2 : ℚ) ^ (2 * k + 1 + 1) := by
      rw [show (-1 / 2 : ℚ) = -(1 / 2) by ring, neg_pow]
      simp [pow_add, pow_mul]
    rw [hneg, sub_self, zero_div, mul_zero]

private noncomputable def centeredBernoulliRat : ℕ → ℚ :=
  Appell.dilate 2
    (Appell.translate (1 / 2 : ℚ) (_root_.bernoulli : ℕ → ℚ))

private theorem Appell.translate_eq_binomialConv_pow
    (c : ℚ) (b : ℕ → ℚ) :
    Appell.translate c b = Bell.binomialConv (fun n ↦ c ^ n) b := by
  funext n
  exact Appell.eval_poly b c n

private theorem binomialConv_translate_neg_translate
    (c : ℚ) (a b : ℕ → ℚ) :
    Bell.binomialConv (Appell.translate (-c) a) (Appell.translate c b) =
      Bell.binomialConv a b := by
  rw [Appell.translate_eq_binomialConv_pow,
    Appell.translate_eq_binomialConv_pow, binomialConv_four_swap]
  have hpowers :
      Bell.binomialConv (fun n : ℕ ↦ (-c) ^ n) (fun n : ℕ ↦ c ^ n) =
        fun n : ℕ ↦ (-c + c) ^ n := by
    funext n
    exact Bell.binomialConv_pow (-c) c n
  rw [hpowers]
  have hzero : (fun n : ℕ ↦ ((-c + c : ℚ) ^ n)) = Bell.unitSeq ℚ := by
    funext n
    cases n <;> simp [Bell.unitSeq]
  rw [hzero, Bell.binomialConv_unitSeq_left]

private theorem binomialConv_centeredUnitUniformRawMomentRat_centeredBernoulliRat :
    Bell.binomialConv centeredUnitUniformRawMomentRat centeredBernoulliRat =
      Bell.unitSeq ℚ := by
  rw [centeredUnitUniformRawMomentRat_eq_affine, centeredBernoulliRat,
    Appell.binomialConv_dilate]
  have htranslate :
      Bell.binomialConv
          (Appell.translate (-1 / 2 : ℚ) unitUniformRawMomentRat)
          (Appell.translate (1 / 2 : ℚ)
            (_root_.bernoulli : ℕ → ℚ)) =
        Bell.binomialConv unitUniformRawMomentRat
          (_root_.bernoulli : ℕ → ℚ) := by
    convert binomialConv_translate_neg_translate (1 / 2 : ℚ)
      unitUniformRawMomentRat (_root_.bernoulli : ℕ → ℚ) using 1
    norm_num
  rw [htranslate, binomialConv_unitUniformRawMomentRat_bernoulli]
  funext n
  cases n <;> simp [Appell.dilate, Bell.unitSeq]

private theorem reciprocal_dilate_centeredUnitUniformRawMomentRat (a : ℚ) :
    Bell.reciprocal (Appell.dilate a centeredUnitUniformRawMomentRat) =
      Appell.dilate a centeredBernoulliRat := by
  symm
  apply Bell.eq_reciprocal_of_binomialConv
  · simp [Appell.dilate, centeredUnitUniformRawMomentRat]
  · rw [Appell.binomialConv_dilate,
      binomialConv_centeredUnitUniformRawMomentRat_centeredBernoulliRat]
    funext n
    cases n <;> simp [Appell.dilate, Bell.unitSeq]

private theorem reciprocal_centeredDyadicPrefixMomentRat_succ (N : ℕ) :
    Bell.reciprocal (centeredDyadicPrefixMomentRat (N + 1)) =
      Bell.binomialConv
        (Bell.reciprocal (centeredDyadicPrefixMomentRat N))
        (Appell.dilate (dyadicPrefixScaleRat (N + 1)) centeredBernoulliRat) := by
  symm
  apply Bell.eq_reciprocal_of_binomialConv
  · exact centeredDyadicPrefixMomentRat_zero (N + 1)
  · change Bell.binomialConv
        (Bell.binomialConv (centeredDyadicPrefixMomentRat N)
          (Appell.dilate (dyadicPrefixScaleRat (N + 1))
            centeredUnitUniformRawMomentRat))
        (Bell.binomialConv
          (Bell.reciprocal (centeredDyadicPrefixMomentRat N))
          (Appell.dilate (dyadicPrefixScaleRat (N + 1))
            centeredBernoulliRat)) = Bell.unitSeq ℚ
    calc
      _ = Bell.binomialConv
            (Bell.binomialConv (centeredDyadicPrefixMomentRat N)
              (Bell.reciprocal (centeredDyadicPrefixMomentRat N)))
            (Bell.binomialConv
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                centeredUnitUniformRawMomentRat)
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                centeredBernoulliRat)) :=
          binomialConv_four_swap _ _ _ _
      _ = Bell.binomialConv (Bell.unitSeq ℚ)
            (Bell.binomialConv
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                centeredUnitUniformRawMomentRat)
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                centeredBernoulliRat)) := by
          rw [Bell.binomialConv_reciprocal _
            (centeredDyadicPrefixMomentRat_zero N)]
      _ = Bell.binomialConv
            (Appell.dilate (dyadicPrefixScaleRat (N + 1))
              centeredUnitUniformRawMomentRat)
            (Appell.dilate (dyadicPrefixScaleRat (N + 1))
              centeredBernoulliRat) :=
          Bell.binomialConv_unitSeq_left _
      _ = Bell.binomialConv
            (Appell.dilate (dyadicPrefixScaleRat (N + 1))
              centeredUnitUniformRawMomentRat)
            (Bell.reciprocal
              (Appell.dilate (dyadicPrefixScaleRat (N + 1))
                centeredUnitUniformRawMomentRat)) := by
          rw [reciprocal_dilate_centeredUnitUniformRawMomentRat]
      _ = Bell.unitSeq ℚ :=
          Bell.binomialConv_reciprocal _ (by
            simp [Appell.dilate, centeredUnitUniformRawMomentRat])

private theorem dilate_centeredBernoulliRat (a : ℚ) :
    Appell.dilate a centeredBernoulliRat =
      Appell.dilate (2 * a)
        (Appell.translate (1 / 2 : ℚ) (_root_.bernoulli : ℕ → ℚ)) := by
  rw [centeredBernoulliRat, Appell.dilate_dilate]
  congr 1
  ring

private theorem eval_poly_dilate_translate_bernoulli
    (s c : ℚ) (hs : s ≠ 0) (n : ℕ) (x : ℚ) :
    (Appell.poly
        (Appell.dilate s
          (Appell.translate c (_root_.bernoulli : ℕ → ℚ))) n).eval x =
      s ^ n * (Polynomial.bernoulli n).eval (x / s + c) := by
  have hst : s * s⁻¹ = (1 : ℚ) := mul_inv_cancel₀ hs
  have h := congrArg (Polynomial.eval x)
    (Appell.poly_affine (_root_.bernoulli : ℕ → ℚ) hst c n)
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, div_eq_mul_inv,
    appell_poly_bernoulli, mul_comm] using h

private theorem eval_poly_dilate_centeredBernoulli_add_sub
    (a : ℚ) (ha : a ≠ 0) (n : ℕ) (x : ℚ) :
    (Appell.poly (Appell.dilate a centeredBernoulliRat) n).eval (x + a) -
        (Appell.poly (Appell.dilate a centeredBernoulliRat) n).eval (x - a) =
      2 * a * (n : ℚ) * x ^ (n - 1) := by
  rw [dilate_centeredBernoulliRat]
  have h2a : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  cases n with
  | zero =>
      simp [Appell.poly_zero, Appell.dilate, Appell.translate]
  | succ n =>
      rw [eval_poly_dilate_translate_bernoulli (2 * a) (1 / 2) h2a,
        eval_poly_dilate_translate_bernoulli (2 * a) (1 / 2) h2a]
      have hplus : (x + a) / (2 * a) + 1 / 2 = 1 + x / (2 * a) := by
        field_simp
        ring
      have hminus : (x - a) / (2 * a) + 1 / 2 = x / (2 * a) := by
        field_simp
        ring
      rw [hplus, hminus, Polynomial.bernoulli_eval_one_add]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      rw [pow_succ, div_pow]
      field_simp [ha]
      ring

private theorem centeredPrefixAppell_eval_add_sub (N n : ℕ) (x : ℚ) :
    (centeredDyadicPrefixAppellPolynomialRat (N + 1) n).eval
          (x + dyadicPrefixScaleRat (N + 1)) -
        (centeredDyadicPrefixAppellPolynomialRat (N + 1) n).eval
          (x - dyadicPrefixScaleRat (N + 1)) =
      2 * dyadicPrefixScaleRat (N + 1) * (n : ℚ) *
        (centeredDyadicPrefixAppellPolynomialRat N (n - 1)).eval x := by
  let a : ℚ := dyadicPrefixScaleRat (N + 1)
  have ha : a ≠ 0 := by simp [a, dyadicPrefixScaleRat]
  cases n with
  | zero =>
      simp [centeredDyadicPrefixAppellPolynomialRat, Appell.poly_zero,
        Bell.reciprocal_zero]
  | succ n =>
      rw [centeredDyadicPrefixAppellPolynomialRat,
        reciprocal_centeredDyadicPrefixMomentRat_succ,
        Appell.poly_binomialConv]
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C]
      rw [← Finset.sum_sub_distrib, Finset.sum_range_succ]
      have hlast :
          ((n + 1).choose (n + 1) : ℚ) *
              Bell.reciprocal (centeredDyadicPrefixMomentRat N) (n + 1) *
                (Appell.poly (Appell.dilate a centeredBernoulliRat) 0).eval (x + a) -
            ((n + 1).choose (n + 1) : ℚ) *
              Bell.reciprocal (centeredDyadicPrefixMomentRat N) (n + 1) *
                (Appell.poly (Appell.dilate a centeredBernoulliRat) 0).eval (x - a) = 0 := by
        simp [Appell.poly_zero, Appell.dilate, centeredBernoulliRat,
          Appell.translate]
      simp only [Nat.sub_self]
      dsimp only [a] at hlast
      rw [hlast, add_zero]
      rw [show n + 1 - 1 = n by omega]
      suffices hmain :
          (∑ r ∈ range (n + 1), (
            ((n + 1).choose r : ℚ) *
                Bell.reciprocal (centeredDyadicPrefixMomentRat N) r *
                  (Appell.poly (Appell.dilate a centeredBernoulliRat)
                    (n + 1 - r)).eval (x + a) -
              ((n + 1).choose r : ℚ) *
                Bell.reciprocal (centeredDyadicPrefixMomentRat N) r *
                  (Appell.poly (Appell.dilate a centeredBernoulliRat)
                    (n + 1 - r)).eval (x - a))) =
            2 * a * (n + 1 : ℚ) *
              (centeredDyadicPrefixAppellPolynomialRat N n).eval x by
        simpa only [a, Nat.cast_add, Nat.cast_one] using hmain
      calc
        _ =
            ∑ r ∈ range (n + 1),
              2 * a * (n + 1 : ℚ) *
                ((n.choose r : ℚ) *
                  Bell.reciprocal (centeredDyadicPrefixMomentRat N) r *
                    x ^ (n - r)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
          have hstep := eval_poly_dilate_centeredBernoulli_add_sub a ha
            (n + 1 - r) x
          have hsub : n + 1 - r - 1 = n - r := by omega
          have hchoose := Nat.choose_mul_succ_eq n r
          have hchooseNat :
              (n + 1).choose r * (n + 1 - r) =
                (n + 1) * n.choose r := by
            calc
              (n + 1).choose r * (n + 1 - r) =
                  n.choose r * (n + 1) := hchoose.symm
              _ = (n + 1) * n.choose r := Nat.mul_comm _ _
          have hchooseQ :
              ((n + 1).choose r : ℚ) *
                  ((n + 1 - r : ℕ) : ℚ) =
                ((n + 1 : ℕ) : ℚ) * (n.choose r : ℚ) := by
            exact_mod_cast hchooseNat
          rw [hsub] at hstep
          calc
            _ = (((n + 1).choose r : ℚ) *
                Bell.reciprocal (centeredDyadicPrefixMomentRat N) r) *
                  ((Appell.poly (Appell.dilate a centeredBernoulliRat)
                    (n + 1 - r)).eval (x + a) -
                    (Appell.poly (Appell.dilate a centeredBernoulliRat)
                      (n + 1 - r)).eval (x - a)) := by ring
            _ = (((n + 1).choose r : ℚ) *
                Bell.reciprocal (centeredDyadicPrefixMomentRat N) r) *
                  (2 * a * ((n + 1 - r : ℕ) : ℚ) *
                    x ^ (n - r)) := by
              rw [hstep]
            _ = 2 * a *
                (((n + 1).choose r : ℚ) *
                  ((n + 1 - r : ℕ) : ℚ)) *
                (Bell.reciprocal (centeredDyadicPrefixMomentRat N) r *
                  x ^ (n - r)) := by ring
            _ = _ := by
              rw [hchooseQ]
              norm_num only [Nat.cast_add, Nat.cast_one]
              ring
        _ = 2 * a * (n + 1 : ℚ) *
              (centeredDyadicPrefixAppellPolynomialRat N n).eval x := by
          rw [centeredDyadicPrefixAppellPolynomialRat,
            eval_poly_eq_sum_rev, Finset.mul_sum]

/-- **Centered Thue--Morse--Rvachev collapse.**  The common-denominator grid
is total at depth zero and equals
`x + (1 - 2⁻ᴺ) - k / 2^(N-1)` whenever `N ≥ 1`. -/
theorem sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat
    (N n : ℕ) (x : ℚ) :
    (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
        (centeredDyadicPrefixAppellPolynomialRat N n).eval
          (x + (1 - dyadicPrefixScaleRat N) -
            (2 * (k.val : ℚ)) / (2 : ℚ) ^ N)) =
      (1 / 2 : ℚ) ^ N.choose 2 * (n.descFactorial N : ℚ) *
        x ^ (n - N) := by
  induction N generalizing n x with
  | zero =>
      simpa [centeredDyadicPrefixAppellPolynomialRat,
        centeredDyadicPrefixMomentRat, dyadicPrefixMomentRat,
        dyadicPrefixScaleRat, thueMorseSign, binaryWeight] using
        (eval_poly_reciprocal_unitSeq_rat n x)
  | succ N ih =>
      have hcard : 2 ^ (N + 1) = 2 * 2 ^ N := by
        rw [pow_succ]
        omega
      rw [hcard]
      let f : ℕ → ℚ := fun k ↦
        (centeredDyadicPrefixAppellPolynomialRat (N + 1) n).eval
          (x + (1 - dyadicPrefixScaleRat (N + 1)) -
            (2 * (k : ℚ)) / (2 : ℚ) ^ (N + 1))
      change (∑ k : Fin (2 * 2 ^ N),
          (thueMorseSign k.val : ℚ) * f k.val) = _
      rw [thueMorse_sum_two_mul]
      have hpair (k : Fin (2 ^ N)) :
          f (2 * k.val) - f (2 * k.val + 1) =
            2 * dyadicPrefixScaleRat (N + 1) * (n : ℚ) *
              (centeredDyadicPrefixAppellPolynomialRat N (n - 1)).eval
                (x + (1 - dyadicPrefixScaleRat N) -
                  (2 * (k.val : ℚ)) / (2 : ℚ) ^ N) := by
        convert centeredPrefixAppell_eval_add_sub N n
          (x + (1 - dyadicPrefixScaleRat N) -
            (2 * (k.val : ℚ)) / (2 : ℚ) ^ N) using 1
        simp [f, dyadicPrefixScaleRat, pow_succ]
        ring_nf
      have hfactor :
          (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
            (2 * dyadicPrefixScaleRat (N + 1) * (n : ℚ) *
              (centeredDyadicPrefixAppellPolynomialRat N (n - 1)).eval
                (x + (1 - dyadicPrefixScaleRat N) -
                  (2 * (k.val : ℚ)) / (2 : ℚ) ^ N))) =
            (2 * dyadicPrefixScaleRat (N + 1) * (n : ℚ)) *
              (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
                (centeredDyadicPrefixAppellPolynomialRat N (n - 1)).eval
                  (x + (1 - dyadicPrefixScaleRat N) -
                    (2 * (k.val : ℚ)) / (2 : ℚ) ^ N)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      simp_rw [hpair]
      rw [hfactor]
      cases n with
      | zero =>
          simp
      | succ n =>
          rw [show n + 1 - 1 = n by omega]
          rw [ih n]
          simp only [Nat.succ_sub_succ_eq_sub, Nat.cast_add, Nat.cast_one,
            Nat.succ_descFactorial_succ]
          have htri : (N + 1).choose 2 = N.choose 2 + N := by
            rw [Nat.choose_succ_succ]
            simp [add_comm]
          rw [htri, pow_add]
          simp [dyadicPrefixScaleRat, pow_succ]
          ring

/-- Successor-indexed centered collapse on the manuscript's literal grid
`x + s_N - k / 2^(N-1)`, for every positive depth `N = m + 1`. -/
theorem sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_succ
    (m n : ℕ) (x : ℚ) :
    (∑ k : Fin (2 ^ (m + 1)), (thueMorseSign k.val : ℚ) *
        (centeredDyadicPrefixAppellPolynomialRat (m + 1) n).eval
          (x + (1 - dyadicPrefixScaleRat (m + 1)) -
            (k.val : ℚ) / (2 : ℚ) ^ m)) =
      (1 / 2 : ℚ) ^ (m + 1).choose 2 *
        (n.descFactorial (m + 1) : ℚ) * x ^ (n - (m + 1)) := by
  convert sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat
    (m + 1) n x using 1
  apply Finset.sum_congr rfl
  intro k _hk
  congr 2
  have hpow : (2 : ℚ) ^ (m + 1) = 2 * (2 : ℚ) ^ m := by
    rw [pow_succ]
    ring
  rw [hpow]
  field_simp

/-- Prouhet cancellation for the centered finite-prefix Appell polynomial
below the block depth. -/
theorem sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_of_lt
    (N n : ℕ) (hn : n < N) (x : ℚ) :
    (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
        (centeredDyadicPrefixAppellPolynomialRat N n).eval
          (x + (1 - dyadicPrefixScaleRat N) -
            (2 * (k.val : ℚ)) / (2 : ℚ) ^ N)) = 0 := by
  rw [sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat,
    Nat.descFactorial_eq_zero_iff_lt.mpr hn, Nat.cast_zero, mul_zero, zero_mul]

/-- The first nonzero centered response is the sign-free constant
`N! 2^{-N(N-1)/2}`. -/
theorem sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_self
    (N : ℕ) (x : ℚ) :
    (∑ k : Fin (2 ^ N), (thueMorseSign k.val : ℚ) *
        (centeredDyadicPrefixAppellPolynomialRat N N).eval
          (x + (1 - dyadicPrefixScaleRat N) -
            (2 * (k.val : ℚ)) / (2 : ℚ) ^ N)) =
      (N.factorial : ℚ) * (1 / 2 : ℚ) ^ N.choose 2 := by
  rw [sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat,
    Nat.descFactorial_self, Nat.sub_self, pow_zero]
  ring

end Fabius
