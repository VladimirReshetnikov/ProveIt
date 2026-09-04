import FabiusFunction.BernoulliRecurrences
import FabiusFunction.GeometricLagrange
import FabiusFunction.RvachevMomentAppell

/-!
# Finite dyadic Appell prefixes and exact recovery

This file gives the coefficient-level finite-convolution model behind the
finite-prefix Appell polynomials.  The definitions do not use the desired
expansion: a depth-`N` prefix moment sequence is built by convolving the
moments of the first `N` independently scaled uniform digits.  Its Appell
sequence is then defined from the binomial-convolution reciprocal.

The full uncentered moments are `halfMoment`; the full centered moments are
`rvachevRawMomentRat`.  Their one-step fixed-point recurrences imply the exact
tail factorizations

`prefix_N ⋆ dilate (2⁻ᴺ) full = full`.

Reciprocal uniqueness turns those factorizations around.  A generic Appell
transform theorem then gives the two printed finite-prefix expansions:

* the Kabaya--Iri prefix is a polynomial-valued polynomial of exact degree
  `n` in `2⁻ᴺ`;
* the centered Rvachev prefix is a polynomial-valued polynomial of exact
  degree `⌊n/2⌋` in `4⁻ᴺ`, because all odd centered moments vanish.

Here "polynomial-valued" is essential in the centered odd case: after a
specialization such as `x = 0`, the leading Appell coefficient can vanish.

Finally the existing geometric Lagrange row evaluates those scale polynomials
at zero.  This recovers the full Appell polynomial from any consecutive block
of prefixes, with bases `1/2` and `1/4`, exactly and with no limiting
argument.

## Main declarations

* `dyadicPrefixMomentRat` is the generic finite convolution of scaled digit
  moments.
* `uncenteredDyadicPrefixMomentRat` and
  `centeredDyadicPrefixMomentRat` specialize it to uniform digits on `[0,1]`
  and `[-1,1]`.
* `Appell.poly_binomialConv` is the reusable Appell transform of a binomial
  convolution.
* `uncenteredDyadicPrefixAppellPolynomialRat_eq_sum` and
  `centeredDyadicPrefixAppellPolynomialRat_eq_sum_even` are the two exact
  prefix expansions.
* `uncenteredDyadicPrefixAppellScalePolynomialRat` and
  `centeredDyadicPrefixAppellScalePolynomialRat` package their free scale
  variables and have the exact degrees asserted in the manuscript.
* `kabayaIriAppellPolynomialRat_eq_sum_prefix` and
  `rvachevAppellPolynomialRat_eq_sum_prefix` are exact geometric Richardson
  recovery at `1/2` and `1/4`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Polynomial

noncomputable section

/-! ## Generic Appell and dilation algebra -/

namespace Appell

/-- **Appell transform of a binomial convolution.**  Multiplying the
coefficient EGF by `a` replaces the `n`-th Appell polynomial by the finite
binomial combination of the original Appell polynomials.  This is the
coefficient-level identity

`exp(Xt) (A(t) B(t)) = A(t) (exp(Xt) B(t))`

over an arbitrary commutative semiring. -/
theorem poly_binomialConv
    {R : Type*} [CommSemiring R] (a b : ℕ → R) (n : ℕ) :
    poly (Bell.binomialConv a b) n =
      ∑ r ∈ range (n + 1),
        C ((n.choose r : R) * a r) * poly b (n - r) := by
  have hmap :
      (fun k ↦ C (Bell.binomialConv a b k)) =
        Bell.binomialConv (fun k ↦ C (a k)) (fun k ↦ C (b k)) := by
    funext k
    exact (Bell.binomialConv_map (C : R →+* R[X]) a b k).symm
  have hpoly :
      Bell.binomialConv (fun k ↦ (X : R[X]) ^ k) (fun k ↦ C (b k)) =
        fun k ↦ poly b k := by
    funext k
    exact (poly_eq_binomialConv b k).symm
  calc
    poly (Bell.binomialConv a b) n =
        Bell.binomialConv (fun k ↦ (X : R[X]) ^ k)
          (fun k ↦ C (Bell.binomialConv a b k)) n :=
      poly_eq_binomialConv _ n
    _ = Bell.binomialConv (fun k ↦ (X : R[X]) ^ k)
          (Bell.binomialConv (fun k ↦ C (a k)) (fun k ↦ C (b k))) n := by
      rw [hmap]
    _ = Bell.binomialConv (fun k ↦ C (a k))
          (Bell.binomialConv (fun k ↦ (X : R[X]) ^ k)
            (fun k ↦ C (b k))) n := by
      rw [← Bell.binomialConv_assoc,
        Bell.binomialConv_comm (fun k ↦ (X : R[X]) ^ k),
        Bell.binomialConv_assoc]
    _ = Bell.binomialConv (fun k ↦ C (a k)) (fun k ↦ poly b k) n := by
      rw [hpoly]
    _ = ∑ r ∈ range (n + 1),
          C ((n.choose r : R) * a r) * poly b (n - r) := by
      rw [Bell.binomialConv_eq_sum_range]
      apply sum_congr rfl
      intro r _hr
      rw [C_mul, C_eq_natCast]
      ring

/-- Dilation of both factors commutes with binomial convolution.  This is
substitution `t ↦ u t` in a product of exponential generating functions. -/
theorem binomialConv_dilate
    {R : Type*} [CommSemiring R] (u : R) (a b : ℕ → R) :
    Bell.binomialConv (dilate u a) (dilate u b) =
      dilate u (Bell.binomialConv a b) := by
  funext n
  exact Bell.binomialConv_pow_mul u a b n

/-- Successive coefficient dilations multiply their scales. -/
theorem dilate_dilate
    {R : Type*} [CommSemiring R] (u v : R) (a : ℕ → R) :
    dilate u (dilate v a) = dilate (u * v) a := by
  funext n
  simp only [dilate, mul_pow]
  ring

end Appell

namespace Fabius

/-! ## Finite digit moments -/

/-- The `r`-th raw moment of a uniform variable on `[0,1]`, in exact rational
arithmetic. -/
def unitUniformRawMomentRat (r : ℕ) : ℚ :=
  (((r + 1 : ℕ) : ℚ))⁻¹

/-- The `r`-th raw moment of a uniform variable on `[-1,1]`.  Even moments
are `1/(r+1)` and odd moments vanish. -/
def centeredUnitUniformRawMomentRat (r : ℕ) : ℚ :=
  if Even r then (((r + 1 : ℕ) : ℚ))⁻¹ else 0

/-- The exact dyadic scale `2⁻ᴺ`. -/
def dyadicPrefixScaleRat (N : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ N

/-- The depth-`N` moment sequence built from a digit moment sequence by
finite binomial convolution.  The successor step appends the digit at scale
`2⁻⁽ᴺ⁺¹⁾`; depth zero is the point mass at zero. -/
def dyadicPrefixMomentRat (digitMoment : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => Bell.unitSeq ℚ
  | N + 1 =>
      Bell.binomialConv (dyadicPrefixMomentRat digitMoment N)
        (Appell.dilate (dyadicPrefixScaleRat (N + 1)) digitMoment)

/-- The raw moments of `X_N = ∑_{j=1}^N 2⁻ʲ V_j`, with independent
`V_j` uniform on `[0,1]`, encoded as a finite convolution. -/
def uncenteredDyadicPrefixMomentRat (N : ℕ) : ℕ → ℚ :=
  dyadicPrefixMomentRat unitUniformRawMomentRat N

/-- The raw moments of `Y_N = ∑_{j=1}^N 2⁻ʲ U_j`, with independent
`U_j` uniform on `[-1,1]`, encoded as a finite convolution. -/
def centeredDyadicPrefixMomentRat (N : ℕ) : ℕ → ℚ :=
  dyadicPrefixMomentRat centeredUnitUniformRawMomentRat N

/-- Every finite dyadic prefix moment sequence has unit zeroth moment,
including the empty prefix. -/
@[simp] theorem dyadicPrefixMomentRat_zero
    (digitMoment : ℕ → ℚ) (hdigit : digitMoment 0 = 1) (N : ℕ) :
    dyadicPrefixMomentRat digitMoment N 0 = 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp [dyadicPrefixMomentRat, Bell.binomialConv,
        Appell.dilate, ih, hdigit]

/-- The uncentered finite prefix has total mass one. -/
@[simp] theorem uncenteredDyadicPrefixMomentRat_zero (N : ℕ) :
    uncenteredDyadicPrefixMomentRat N 0 = 1 := by
  exact dyadicPrefixMomentRat_zero unitUniformRawMomentRat (by
    simp [unitUniformRawMomentRat]) N

/-- The centered finite prefix has total mass one. -/
@[simp] theorem centeredDyadicPrefixMomentRat_zero (N : ℕ) :
    centeredDyadicPrefixMomentRat N 0 = 1 := by
  exact dyadicPrefixMomentRat_zero centeredUnitUniformRawMomentRat (by
    simp [centeredUnitUniformRawMomentRat]) N

/-! ## Full one-step fixed points and tail factorization -/

private theorem sum_range_even {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : ℕ → R) :
    (∑ x ∈ range (n + 1), if 2 ∣ x then f x else 0) =
      ∑ k ∈ range (n / 2 + 1), f (2 * k) := by
  rw [← Finset.sum_filter]
  have hfilter :
      (range (n + 1)).filter (fun x => 2 ∣ x) =
        (range (n / 2 + 1)).image (fun k => 2 * k) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hx, ⟨k, rfl⟩⟩
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, ⟨k, rfl⟩⟩
  rw [hfilter, Finset.sum_image]
  intro a _ha b _hb hab
  change 2 * a = 2 * b at hab
  omega

private theorem binomialConv_eq_zero_of_odd
    {R : Type*} [Semiring R] {a b : ℕ → R}
    (ha : ∀ {r}, Odd r → a r = 0) (hb : ∀ {r}, Odd r → b r = 0)
    {n : ℕ} (hn : Odd n) :
    Bell.binomialConv a b n = 0 := by
  rw [Bell.binomialConv_eq_sum_range]
  apply sum_eq_zero
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rcases Nat.even_or_odd k with hkeven | hkodd
  · have hsub : Odd (n - k) := Nat.Odd.sub_even hkn hn hkeven
    rw [hb hsub, mul_zero, mul_zero]
  · rw [ha hkodd, zero_mul, mul_zero]

private theorem rvachevRawMomentRat_eq_zero_of_odd
    {r : ℕ} (hr : Odd r) : rvachevRawMomentRat r = 0 := by
  obtain ⟨k, rfl⟩ := hr
  exact rvachevRawMomentRat_odd k

private theorem uncenteredFullMoment_fixedPoint :
    Bell.binomialConv
        (Appell.dilate (1 / 2 : ℚ) unitUniformRawMomentRat)
        (Appell.dilate (1 / 2 : ℚ) halfMoment) =
      halfMoment := by
  rw [Appell.binomialConv_dilate]
  funext n
  change (1 / 2 : ℚ) ^ n *
      Bell.binomialConv unitUniformRawMomentRat halfMoment n = halfMoment n
  rw [Bell.binomialConv_eq_sum_range]
  have hsum :
      (∑ k ∈ range (n + 1),
          (n.choose k : ℚ) *
            (unitUniformRawMomentRat k * halfMoment (n - k))) =
        (∑ k ∈ range (n + 1),
          (n + 1).choose k * halfMoment k) / (n + 1 : ℚ) := by
    rw [← Finset.sum_range_reflect
      (fun k => (n.choose k : ℚ) *
        (unitUniformRawMomentRat k * halfMoment (n - k))) (n + 1)]
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    simp only [Nat.add_sub_cancel]
    rw [Nat.choose_symm hkn, Nat.sub_sub_self hkn,
      unitUniformRawMomentRat]
    have hnat := Nat.choose_mul_succ_eq n k
    have hsub : n + 1 - k = n - k + 1 := by omega
    rw [hsub] at hnat
    have hrat :
        (n.choose k : ℚ) * (n + 1 : ℚ) =
          ((n + 1).choose k : ℚ) * (n - k + 1 : ℚ) := by
      exact_mod_cast hnat
    have hn1 : (n + 1 : ℚ) ≠ 0 := by positivity
    have hnk1 : ((n - k + 1 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (n - k)
    push_cast [Nat.cast_sub hkn] at hrat hnk1 ⊢
    field_simp [hn1, hnk1]
    linear_combination hrat * halfMoment k
  rw [hsum, ← halfMoment_original_recurrence n]
  have hn1 : (n + 1 : ℚ) ≠ 0 := by positivity
  norm_num [div_pow]
  field_simp [hn1]

private theorem centeredFullMoment_fixedPoint :
    Bell.binomialConv
        (Appell.dilate (1 / 2 : ℚ) centeredUnitUniformRawMomentRat)
        (Appell.dilate (1 / 2 : ℚ) rvachevRawMomentRat) =
      rvachevRawMomentRat := by
  rw [Appell.binomialConv_dilate]
  funext n
  change (1 / 2 : ℚ) ^ n *
      Bell.binomialConv centeredUnitUniformRawMomentRat
        rvachevRawMomentRat n = rvachevRawMomentRat n
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨d, hd⟩ := heven
    have hdn : n = 2 * d := by omega
    rw [hdn]
    rw [rvachevRawMomentRat_even, Bell.binomialConv_eq_sum_range]
    have hsum :
        (∑ k ∈ range (2 * d + 1),
            ((2 * d).choose k : ℚ) *
              (centeredUnitUniformRawMomentRat k *
                rvachevRawMomentRat (2 * d - k))) =
          ∑ j ∈ range (d + 1),
            ((2 * d).choose (2 * j) : ℚ) *
              (((2 * j + 1 : ℕ) : ℚ)⁻¹ * moment (d - j)) := by
      calc
        (∑ k ∈ range (2 * d + 1),
            ((2 * d).choose k : ℚ) *
              (centeredUnitUniformRawMomentRat k *
                rvachevRawMomentRat (2 * d - k))) =
            ∑ k ∈ range (2 * d + 1), if 2 ∣ k then
              ((2 * d).choose k : ℚ) *
                ((((k + 1 : ℕ) : ℚ))⁻¹ *
                  rvachevRawMomentRat (2 * d - k)) else 0 := by
              apply sum_congr rfl
              intro k _hk
              by_cases hk : 2 ∣ k
              · have hkeven : Even k := even_iff_two_dvd.mpr hk
                rw [if_pos hk, centeredUnitUniformRawMomentRat,
                  if_pos hkeven]
              · have hkeven : ¬ Even k := fun h =>
                  hk (even_iff_two_dvd.mp h)
                rw [if_neg hk, centeredUnitUniformRawMomentRat,
                  if_neg hkeven, zero_mul, mul_zero]
        _ = ∑ j ∈ range (d + 1),
              ((2 * d).choose (2 * j) : ℚ) *
                ((((2 * j + 1 : ℕ) : ℚ))⁻¹ *
                  rvachevRawMomentRat (2 * d - 2 * j)) := by
              rw [sum_range_even]
              have hbound : (2 * d) / 2 = d := by omega
              rw [hbound]
        _ = ∑ j ∈ range (d + 1),
              ((2 * d).choose (2 * j) : ℚ) *
                ((((2 * j + 1 : ℕ) : ℚ))⁻¹ * moment (d - j)) := by
              apply sum_congr rfl
              intro j hj
              have hjd : j ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hj)
              rw [show 2 * d - 2 * j = 2 * (d - j) by omega,
                rvachevRawMomentRat_even]
    rw [hsum]
    have hsum' :
        (∑ j ∈ range (d + 1),
            ((2 * d).choose (2 * j) : ℚ) *
              ((((2 * j + 1 : ℕ) : ℚ))⁻¹ * moment (d - j))) =
          (∑ j ∈ range (d + 1),
            ((2 * d + 1).choose (2 * j) : ℚ) * moment j) /
              (2 * d + 1 : ℚ) := by
      rw [← Finset.sum_range_reflect
        (fun j => ((2 * d).choose (2 * j) : ℚ) *
          ((((2 * j + 1 : ℕ) : ℚ))⁻¹ * moment (d - j))) (d + 1)]
      rw [Finset.sum_div]
      apply sum_congr rfl
      intro j hj
      have hjd : j ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hj)
      simp only [Nat.add_sub_cancel]
      rw [Nat.sub_sub_self hjd]
      have hindex : 2 * (d - j) = 2 * d - 2 * j := by omega
      rw [hindex, Nat.choose_symm (by omega : 2 * j ≤ 2 * d)]
      have hnat := Nat.choose_mul_succ_eq (2 * d) (2 * j)
      have hsub : 2 * d + 1 - 2 * j = 2 * (d - j) + 1 := by omega
      rw [hsub] at hnat
      have hrat :
          ((2 * d).choose (2 * j) : ℚ) * (2 * d + 1 : ℚ) =
            ((2 * d + 1).choose (2 * j) : ℚ) *
              (2 * (d - j) + 1 : ℚ) := by
        exact_mod_cast hnat
      have hden1 : (2 * d + 1 : ℚ) ≠ 0 := by positivity
      have hden2 : ((2 * (d - j) + 1 : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero (2 * (d - j))
      have hcast : (((2 * d - 2 * j : ℕ) : ℚ)) =
          2 * ((d : ℚ) - j) := by
        rw [Nat.cast_sub (by omega : 2 * j ≤ 2 * d)]
        push_cast
        ring
      push_cast [Nat.cast_sub hjd] at hrat hden2 ⊢
      rw [hcast]
      field_simp [hden1, hden2]
      linear_combination hrat * moment j
    rw [hsum', ← moment_original_recurrence d]
    have hden : (2 * d + 1 : ℚ) ≠ 0 := by positivity
    norm_num [div_pow, pow_mul]
    field_simp [hden]
  · rw [rvachevRawMomentRat_eq_zero_of_odd hodd]
    have hconv : Bell.binomialConv centeredUnitUniformRawMomentRat
        rvachevRawMomentRat n = 0 :=
      binomialConv_eq_zero_of_odd
        (fun {_} hr => by
          simp [centeredUnitUniformRawMomentRat,
            Nat.not_even_iff_odd.mpr hr])
        rvachevRawMomentRat_eq_zero_of_odd hodd
    rw [hconv, mul_zero]

/-- **Generic finite-prefix tail factorization.**  If a full moment sequence
is the convolution of one half-scaled digit with an independent half-scaled
copy of itself, then its first `N` dyadic digits convolved with the tail at
scale `2⁻ᴺ` recover the full sequence. -/
theorem dyadicPrefixMomentRat_binomialConv_tail
    (digitMoment fullMoment : ℕ → ℚ)
    (hfixed : Bell.binomialConv
        (Appell.dilate (1 / 2 : ℚ) digitMoment)
        (Appell.dilate (1 / 2 : ℚ) fullMoment) = fullMoment)
    (N : ℕ) :
    Bell.binomialConv (dyadicPrefixMomentRat digitMoment N)
        (Appell.dilate (dyadicPrefixScaleRat N) fullMoment) =
      fullMoment := by
  induction N with
  | zero =>
      simp only [dyadicPrefixMomentRat, dyadicPrefixScaleRat, pow_zero]
      have hdilate : Appell.dilate (1 : ℚ) fullMoment = fullMoment := by
        funext n
        simp [Appell.dilate]
      rw [hdilate, Bell.binomialConv_unitSeq_left]
  | succ N ih =>
      have hscale : dyadicPrefixScaleRat (N + 1) =
          dyadicPrefixScaleRat N * (1 / 2 : ℚ) := by
        simp only [dyadicPrefixScaleRat, pow_succ]
      have hstep :
          Bell.binomialConv
              (Appell.dilate (dyadicPrefixScaleRat (N + 1)) digitMoment)
              (Appell.dilate (dyadicPrefixScaleRat (N + 1)) fullMoment) =
            Appell.dilate (dyadicPrefixScaleRat N) fullMoment := by
        rw [hscale]
        rw [← Appell.dilate_dilate, ← Appell.dilate_dilate,
          Appell.binomialConv_dilate, hfixed]
      calc
        Bell.binomialConv (dyadicPrefixMomentRat digitMoment (N + 1))
            (Appell.dilate (dyadicPrefixScaleRat (N + 1)) fullMoment) =
          Bell.binomialConv
            (Bell.binomialConv (dyadicPrefixMomentRat digitMoment N)
              (Appell.dilate (dyadicPrefixScaleRat (N + 1)) digitMoment))
            (Appell.dilate (dyadicPrefixScaleRat (N + 1)) fullMoment) := by
              rw [dyadicPrefixMomentRat]
        _ = Bell.binomialConv (dyadicPrefixMomentRat digitMoment N)
              (Bell.binomialConv
                (Appell.dilate (dyadicPrefixScaleRat (N + 1)) digitMoment)
                (Appell.dilate (dyadicPrefixScaleRat (N + 1)) fullMoment)) :=
          Bell.binomialConv_assoc _ _ _
        _ = Bell.binomialConv (dyadicPrefixMomentRat digitMoment N)
              (Appell.dilate (dyadicPrefixScaleRat N) fullMoment) := by
          rw [hstep]
        _ = fullMoment := ih

/-- The uncentered finite prefix and its scaled infinite tail have the full
Kabaya--Iri moment sequence `halfMoment`. -/
theorem binomialConv_uncenteredDyadicPrefixMomentRat_tail (N : ℕ) :
    Bell.binomialConv (uncenteredDyadicPrefixMomentRat N)
        (Appell.dilate (dyadicPrefixScaleRat N) halfMoment) = halfMoment := by
  exact dyadicPrefixMomentRat_binomialConv_tail
    unitUniformRawMomentRat halfMoment uncenteredFullMoment_fixedPoint N

/-- The centered finite prefix and its scaled infinite tail have the full
Rvachev moment sequence. -/
theorem binomialConv_centeredDyadicPrefixMomentRat_tail (N : ℕ) :
    Bell.binomialConv (centeredDyadicPrefixMomentRat N)
        (Appell.dilate (dyadicPrefixScaleRat N) rvachevRawMomentRat) =
      rvachevRawMomentRat := by
  exact dyadicPrefixMomentRat_binomialConv_tail
    centeredUnitUniformRawMomentRat rvachevRawMomentRat
      centeredFullMoment_fixedPoint N

/-! ## Prefix Appell sequences -/

/-- The rational infinite Kabaya--Iri Appell polynomial attached to the
uncentered moment sequence `halfMoment`. -/
noncomputable def kabayaIriAppellPolynomialRat (n : ℕ) : ℚ[X] :=
  Appell.poly (Bell.reciprocal halfMoment) n

/-- The rational Appell polynomial of the uncentered depth-`N` prefix. -/
noncomputable def uncenteredDyadicPrefixAppellPolynomialRat
    (N n : ℕ) : ℚ[X] :=
  Appell.poly (Bell.reciprocal (uncenteredDyadicPrefixMomentRat N)) n

/-- The rational Appell polynomial of the centered depth-`N` prefix. -/
noncomputable def centeredDyadicPrefixAppellPolynomialRat
    (N n : ℕ) : ℚ[X] :=
  Appell.poly (Bell.reciprocal (centeredDyadicPrefixMomentRat N)) n

private theorem reciprocal_prefix_eq_binomialConv_tail
    (prefixMoment fullMoment tailMoment : ℕ → ℚ)
    (hprefix0 : prefixMoment 0 = 1) (hfull0 : fullMoment 0 = 1)
    (hfactor : Bell.binomialConv prefixMoment tailMoment = fullMoment) :
    Bell.reciprocal prefixMoment =
      Bell.binomialConv tailMoment (Bell.reciprocal fullMoment) := by
  symm
  apply Bell.eq_reciprocal_of_binomialConv hprefix0
  rw [← Bell.binomialConv_assoc, hfactor,
    Bell.binomialConv_reciprocal fullMoment hfull0]

/-- **Exact uncentered finite-prefix expansion.**  This is the printed
formula

`P⁽ᴺ⁾_n = ∑_{r=0}^n C(n,r) μ_r 2⁻ᴺʳ P_{n-r}`

with `μ_r = halfMoment r`.  Depth zero is included. -/
theorem uncenteredDyadicPrefixAppellPolynomialRat_eq_sum (N n : ℕ) :
    uncenteredDyadicPrefixAppellPolynomialRat N n =
      ∑ r ∈ range (n + 1),
        C ((n.choose r : ℚ) * halfMoment r *
          dyadicPrefixScaleRat N ^ r) *
            kabayaIriAppellPolynomialRat (n - r) := by
  have hrecip :
      Bell.reciprocal (uncenteredDyadicPrefixMomentRat N) =
        Bell.binomialConv (Appell.dilate (dyadicPrefixScaleRat N) halfMoment)
          (Bell.reciprocal halfMoment) :=
    reciprocal_prefix_eq_binomialConv_tail
      (uncenteredDyadicPrefixMomentRat N) halfMoment
      (Appell.dilate (dyadicPrefixScaleRat N) halfMoment)
      (uncenteredDyadicPrefixMomentRat_zero N) halfMoment_zero
      (binomialConv_uncenteredDyadicPrefixMomentRat_tail N)
  rw [uncenteredDyadicPrefixAppellPolynomialRat, hrecip,
    Appell.poly_binomialConv]
  apply sum_congr rfl
  intro r _hr
  simp only [Appell.dilate, kabayaIriAppellPolynomialRat]
  congr 1
  ring_nf

/-- **Exact centered finite-prefix expansion.**  Pairing away the odd raw
moments gives the printed formula

`A⁽ᴺ⁾_n = ∑_{j=0}^{⌊n/2⌋} C(n,2j) m_{2j} 4⁻ᴺʲ A_{n-2j}`,

where the manuscript's `m_{2j}` is the executable `moment j`. -/
theorem centeredDyadicPrefixAppellPolynomialRat_eq_sum_even (N n : ℕ) :
    centeredDyadicPrefixAppellPolynomialRat N n =
      ∑ j ∈ range (n / 2 + 1),
        C ((n.choose (2 * j) : ℚ) * moment j *
          ((1 / 4 : ℚ) ^ N) ^ j) *
            rvachevAppellPolynomialRat (n - 2 * j) := by
  have hrecip :
      Bell.reciprocal (centeredDyadicPrefixMomentRat N) =
        Bell.binomialConv
          (Appell.dilate (dyadicPrefixScaleRat N) rvachevRawMomentRat)
          rvachevReciprocalMomentRat :=
    reciprocal_prefix_eq_binomialConv_tail
      (centeredDyadicPrefixMomentRat N) rvachevRawMomentRat
      (Appell.dilate (dyadicPrefixScaleRat N) rvachevRawMomentRat)
      (centeredDyadicPrefixMomentRat_zero N) rvachevRawMomentRat_zero
      (binomialConv_centeredDyadicPrefixMomentRat_tail N)
  rw [centeredDyadicPrefixAppellPolynomialRat, hrecip,
    Appell.poly_binomialConv]
  calc
    (∑ r ∈ range (n + 1),
        C ((n.choose r : ℚ) *
          Appell.dilate (dyadicPrefixScaleRat N) rvachevRawMomentRat r) *
            Appell.poly rvachevReciprocalMomentRat (n - r)) =
      ∑ r ∈ range (n + 1), if 2 ∣ r then
        C ((n.choose r : ℚ) * dyadicPrefixScaleRat N ^ r *
          moment (r / 2)) * rvachevAppellPolynomialRat (n - r) else 0 := by
      apply sum_congr rfl
      intro r _hr
      by_cases hr : 2 ∣ r
      · rw [if_pos hr]
        simp only [Appell.dilate, rvachevRawMomentRat,
          if_pos hr, rvachevAppellPolynomialRat]
        congr 1
        ring_nf
      · rw [if_neg hr]
        simp [Appell.dilate, rvachevRawMomentRat, hr]
    _ = ∑ j ∈ range (n / 2 + 1),
        C ((n.choose (2 * j) : ℚ) * dyadicPrefixScaleRat N ^ (2 * j) *
          moment j) * rvachevAppellPolynomialRat (n - 2 * j) := by
      rw [sum_range_even]
      apply sum_congr rfl
      intro j _hj
      have hhalf : (2 * j) / 2 = j := by omega
      rw [hhalf]
    _ = ∑ j ∈ range (n / 2 + 1),
        C ((n.choose (2 * j) : ℚ) * moment j *
          ((1 / 4 : ℚ) ^ N) ^ j) *
            rvachevAppellPolynomialRat (n - 2 * j) := by
      apply sum_congr rfl
      intro j _hj
      congr 1
      have hscale : dyadicPrefixScaleRat N ^ (2 * j) =
          ((1 / 4 : ℚ) ^ N) ^ j := by
        calc
          dyadicPrefixScaleRat N ^ (2 * j) =
              (1 / 2 : ℚ) ^ (N * (2 * j)) := by
            simpa only [dyadicPrefixScaleRat] using
              (pow_mul (1 / 2 : ℚ) N (2 * j)).symm
          _ = (1 / 2 : ℚ) ^ (2 * (N * j)) := by
            congr 1
            ring
          _ = ((1 / 2 : ℚ) ^ 2) ^ (N * j) := by
            rw [pow_mul]
          _ = (((1 / 2 : ℚ) ^ 2) ^ N) ^ j := by
            rw [pow_mul]
          _ = ((1 / 4 : ℚ) ^ N) ^ j := by norm_num
      rw [hscale]
      ring_nf

/-! ## Exact polynomial dependence on the free truncation scale -/

/-- The uncentered prefix Appell polynomial as a polynomial in a free scale
variable, with coefficients in `ℚ[X]`.  Evaluating the outer variable at
`2⁻ᴺ` gives the depth-`N` prefix. -/
noncomputable def uncenteredDyadicPrefixAppellScalePolynomialRat
    (n : ℕ) : Polynomial (Polynomial ℚ) :=
  ∑ r ∈ range (n + 1), Polynomial.monomial r
    (C ((n.choose r : ℚ) * halfMoment r) *
      kabayaIriAppellPolynomialRat (n - r))

/-- The centered prefix Appell polynomial as a polynomial in the free
quarter-scale variable, with coefficients in `ℚ[X]`.  Evaluating the outer
variable at `4⁻ᴺ` gives the depth-`N` prefix. -/
noncomputable def centeredDyadicPrefixAppellScalePolynomialRat
    (n : ℕ) : Polynomial (Polynomial ℚ) :=
  ∑ r ∈ range (n / 2 + 1), Polynomial.monomial r
    (C ((n.choose (2 * r) : ℚ) * moment r) *
      rvachevAppellPolynomialRat (n - 2 * r))

/-- Evaluating the free-scale uncentered polynomial at `2⁻ᴺ` is exactly
the depth-`N` finite-prefix Appell polynomial. -/
theorem uncenteredDyadicPrefixAppellPolynomialRat_eq_eval_scale (N n : ℕ) :
    uncenteredDyadicPrefixAppellPolynomialRat N n =
      (uncenteredDyadicPrefixAppellScalePolynomialRat n).eval
        (C (dyadicPrefixScaleRat N)) := by
  rw [uncenteredDyadicPrefixAppellPolynomialRat_eq_sum,
    uncenteredDyadicPrefixAppellScalePolynomialRat,
    Polynomial.eval_finsetSum]
  apply sum_congr rfl
  intro r _hr
  rw [Polynomial.eval_monomial, C_mul, C_pow]
  ring

/-- Evaluating the free quarter-scale centered polynomial at `4⁻ᴺ` is
exactly the depth-`N` finite-prefix Appell polynomial. -/
theorem centeredDyadicPrefixAppellPolynomialRat_eq_eval_scale (N n : ℕ) :
    centeredDyadicPrefixAppellPolynomialRat N n =
      (centeredDyadicPrefixAppellScalePolynomialRat n).eval
        (C ((1 / 4 : ℚ) ^ N)) := by
  rw [centeredDyadicPrefixAppellPolynomialRat_eq_sum_even,
    centeredDyadicPrefixAppellScalePolynomialRat,
    Polynomial.eval_finsetSum]
  apply sum_congr rfl
  intro r _hr
  rw [Polynomial.eval_monomial, C_mul, C_pow]
  ring

/-- The polynomial-valued uncentered prefix has exact degree `n` in its free
scale variable.  Its top coefficient is nonzero because `halfMoment n > 0`.
-/
@[simp] theorem natDegree_uncenteredDyadicPrefixAppellScalePolynomialRat
    (n : ℕ) :
    (uncenteredDyadicPrefixAppellScalePolynomialRat n).natDegree = n := by
  classical
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold uncenteredDyadicPrefixAppellScalePolynomialRat
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    have hmono :
        (Polynomial.monomial r
          (C ((n.choose r : ℚ) * halfMoment r) *
            kabayaIriAppellPolynomialRat (n - r)) :
          Polynomial (Polynomial ℚ)).natDegree ≤ r :=
      Polynomial.natDegree_monomial_le _
    exact hmono.trans (Nat.lt_succ_iff.mp (mem_range.mp hr))
  · unfold uncenteredDyadicPrefixAppellScalePolynomialRat
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
      simpa [kabayaIriAppellPolynomialRat] using
        (Polynomial.C_ne_zero.mpr (halfMoment_pos n).ne' :
          (C (halfMoment n) : ℚ[X]) ≠ 0)
    · intro r _hr hrn
      rw [Polynomial.coeff_monomial, if_neg hrn]
    · simp

/-- The centered prefix has exact outer degree `⌊n/2⌋` in its free
quarter-scale variable.  This is an equality in `Polynomial (Polynomial ℚ)`;
a later pointwise specialization in the inner variable can lower the degree.
-/
@[simp] theorem natDegree_centeredDyadicPrefixAppellScalePolynomialRat
    (n : ℕ) :
    (centeredDyadicPrefixAppellScalePolynomialRat n).natDegree = n / 2 := by
  classical
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold centeredDyadicPrefixAppellScalePolynomialRat
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    have hmono :
        (Polynomial.monomial r
          (C ((n.choose (2 * r) : ℚ) * moment r) *
            rvachevAppellPolynomialRat (n - 2 * r)) :
          Polynomial (Polynomial ℚ)).natDegree ≤ r :=
      Polynomial.natDegree_monomial_le _
    exact hmono.trans (Nat.lt_succ_iff.mp (mem_range.mp hr))
  · unfold centeredDyadicPrefixAppellScalePolynomialRat
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (n / 2)]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
      have hindex : 2 * (n / 2) ≤ n := by omega
      have hchoose : (n.choose (2 * (n / 2)) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hindex)
      have hhalf : halfMoment (2 * (n / 2) + 1) ≠ 0 :=
        (halfMoment_pos (2 * (n / 2) + 1)).ne'
      rw [halfMoment_odd_eq_moment] at hhalf
      have hmoment : moment (n / 2) ≠ 0 := right_ne_zero_of_mul hhalf
      apply mul_ne_zero
      · exact Polynomial.C_ne_zero.mpr (mul_ne_zero hchoose hmoment)
      · exact (monic_rvachevAppellPolynomialRat
          (n - 2 * (n / 2))).ne_zero
    · intro r _hr hrn
      rw [Polynomial.coeff_monomial, if_neg hrn]
    · simp

private theorem uncenteredPrefixAppell_geometricModes (N n : ℕ) :
    uncenteredDyadicPrefixAppellPolynomialRat N n =
      kabayaIriAppellPolynomialRat n +
        ∑ d ∈ range n, dyadicPrefixScaleRat N ^ (d + 1) •
          ((n.choose (d + 1) : ℚ) * halfMoment (d + 1)) •
            kabayaIriAppellPolynomialRat (n - (d + 1)) := by
  rw [uncenteredDyadicPrefixAppellPolynomialRat_eq_sum,
    Finset.sum_range_succ', add_comm]
  simp only [Nat.choose_zero_right, Nat.cast_one, halfMoment_zero,
    dyadicPrefixScaleRat, pow_zero, mul_one, C_1, one_mul,
    Polynomial.smul_eq_C_mul]
  congr 1
  apply sum_congr rfl
  intro d _hd
  simp only [C_mul]
  ring_nf

private theorem centeredPrefixAppell_geometricModes (N n : ℕ) :
    centeredDyadicPrefixAppellPolynomialRat N n =
      rvachevAppellPolynomialRat n +
        ∑ d ∈ range (n / 2), ((1 / 4 : ℚ) ^ N) ^ (d + 1) •
          ((n.choose (2 * (d + 1)) : ℚ) * moment (d + 1)) •
            rvachevAppellPolynomialRat (n - 2 * (d + 1)) := by
  rw [centeredDyadicPrefixAppellPolynomialRat_eq_sum_even,
    Finset.sum_range_succ', add_comm]
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one, moment_zero,
    pow_zero, mul_one, C_1, one_mul, Polynomial.smul_eq_C_mul]
  congr 1
  apply sum_congr rfl
  intro d _hd
  simp only [C_mul]
  ring_nf

/-- **Exact uncentered q-Richardson recovery.**  For every starting depth
`N`, the full degree-`n` Kabaya--Iri polynomial is the geometric Lagrange
combination of the `n+1` consecutive prefixes `N,…,N+n`, with base `1/2`.
-/
theorem kabayaIriAppellPolynomialRat_eq_sum_prefix (N n : ℕ) :
    kabayaIriAppellPolynomialRat n =
      ∑ j ∈ range (n + 1),
        geometricLagrangeWeight (1 / 2 : ℚ) n j •
          uncenteredDyadicPrefixAppellPolynomialRat (N + j) n := by
  have hnode : Set.InjOn (fun j : ℕ => (1 / 2 : ℚ) ^ j)
      (range (n + 1)) :=
    (pow_right_injective₀ (a := (1 / 2 : ℚ)) (by norm_num)
      (by norm_num)).injOn
  symm
  apply geometricLagrange_richardson_exact_of_eq
    (1 / 2 : ℚ) n N hnode
    (fun m => uncenteredDyadicPrefixAppellPolynomialRat m n)
    (kabayaIriAppellPolynomialRat n)
    (fun d => ((n.choose (d + 1) : ℚ) * halfMoment (d + 1)) •
      kabayaIriAppellPolynomialRat (n - (d + 1)))
  intro j _hj
  rw [uncenteredPrefixAppell_geometricModes]
  congr 1

/-- **Exact centered q-Richardson recovery.**  Put `d = ⌊n/2⌋`.  For
every starting depth `N`, the full centered degree-`n` Rvachev--Appell
polynomial is the geometric Lagrange combination of the `d+1` consecutive
prefixes `N,…,N+d`, with base `1/4`. -/
theorem rvachevAppellPolynomialRat_eq_sum_prefix (N n : ℕ) :
    rvachevAppellPolynomialRat n =
      ∑ j ∈ range (n / 2 + 1),
        geometricLagrangeWeight (1 / 4 : ℚ) (n / 2) j •
          centeredDyadicPrefixAppellPolynomialRat (N + j) n := by
  have hnode : Set.InjOn (fun j : ℕ => (1 / 4 : ℚ) ^ j)
      (range (n / 2 + 1)) :=
    (pow_right_injective₀ (a := (1 / 4 : ℚ)) (by norm_num)
      (by norm_num)).injOn
  symm
  apply geometricLagrange_richardson_exact_of_eq
    (1 / 4 : ℚ) (n / 2) N hnode
    (fun m => centeredDyadicPrefixAppellPolynomialRat m n)
    (rvachevAppellPolynomialRat n)
    (fun d => ((n.choose (2 * (d + 1)) : ℚ) * moment (d + 1)) •
      rvachevAppellPolynomialRat (n - 2 * (d + 1)))
  intro j _hj
  rw [centeredPrefixAppell_geometricModes]

end Fabius

end
