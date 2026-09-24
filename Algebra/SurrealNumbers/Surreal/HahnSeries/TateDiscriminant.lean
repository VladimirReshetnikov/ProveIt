import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import Surreal.Algebra.TateCubicNode
import Surreal.HahnSeries.Evaluation
import Surreal.HahnSeries.Regroup
import Surreal.HahnSeries.StandardPart

/-!
# Discriminant and modular invariant of the Hahn--Tate curve

This file proves `tate:prop:discriminant` of
`docs/surcomplex/hahn-tate-uniformization/article.tex`, except for the product formula of
`tate:eq:Delta` (pending below), for the Tate curve
`tateCurve q : y² + xy = x³ + a₄(q)x + a₆(q)` of `Surreal/Algebra/TateCubicNode.lean` over
`K = k⟦Γ⟧`. Here `k` is any field with `(12 : k) ≠ 0` (the source takes `ℂ`, and its second
route any field of characteristic zero), `Γ` is any linearly ordered abelian group, `v` is
`orderTop`, and `q` satisfies `v(q) = α` with `0 < α` in `Γ`.

* First sentence (integer power series): `tateSum_eq_heval` shows that `s_j(q)` is the Hahn
  evaluation `PowerSeries.heval q` of the integer power series `lambertSeries j = ∑ σ_j(N) X^N`.
  The proof regroups the jointly summable Lambert double family `lambertDouble` by rows
  (`hsum_lambertDouble_row`) and by `N = (n+1)(m+1)` (`hsum_lambertDouble_fiber`), using
  `Surreal.HahnSeries.hsum_regroup`. Hence `tateA4_eq_heval` and `tateA6_eq_heval` for the
  integer series `a4Series` and `a6Series`. The coefficients `-(5σ₃(N) + 7σ₅(N))/12` of
  `a6Series` are integers by `twelve_dvd_sigma`, which rests on
  `twelve_dvd_five_mul_pow_three_add_seven_mul_pow_five` (`12 ∣ 5m³ + 7m⁵`). Finally
  `tateCurve_Δ_eq_heval`: `Δ(q)` is the Hahn evaluation of the integer power series
  `discrFormula a4Series a6Series`.
* `tate:eq:Delta`, valuation clause: `tateCurve_Δ` is the discriminant formula obtained from
  `b₂ = 1`, `b₄ = 2a₄`, `b₆ = 4a₆`, `b₈ = a₆ - a₄²`; `two_nsmul_le_orderTop_tateCurve_Δ_sub`
  gives `v(Δ(q) - q) ≥ 2α`, `orderTop_tateCurve_Δ` gives `v(Δ(q)) = α`, and
  `leadingCoeff_tateCurve_Δ` identifies the leading coefficient with that of `q`. To fifth
  order, `five_nsmul_le_orderTop_tateCurve_Δ_sub` proves
  `Δ(q) = q - 24q² + 252q³ - 1472q⁴ + O(q⁵)`. These four coefficients agree with those of
  `q ∏ (1 - qⁿ)²⁴` (a numerical remark, not a Lean statement).
* Last sentence: `tateCurve_Δ_ne_zero`, `isElliptic_tateCurve` (Mathlib's
  `WeierstrassCurve.IsElliptic`) and `tateCurve_equation_iff_nonsingular` (every affine point is
  nonsingular).
* `tate:eq:j`: `tateCurve_j` (`j = c₄³/Δ`, with `c₄ = 1 - 48a₄` by `tateCurve_c₄`),
  `le_orderTop_tateCurve_j_mul_sub_one` (`v(j(q) q - 1) ≥ α`), `orderTop_tateCurve_j`
  (`v(j(q)) = -α`, leading coefficient `lc(q)⁻¹`), and `le_orderTop_tateCurve_j_sub`: the
  displayed expansion `j(q) = q⁻¹ + 744 + 196884q + 21493760q² + O(q³)`, i.e. the difference
  has valuation at least `3α`. `mul_tateCurve_j_eq_heval` shows that `q j(q)` is the Hahn
  evaluation of the integer power series `jSeries = c₄³ (Δ/X)⁻¹`: `Δ/X` (`discrUnit`) has
  constant coefficient `1` (`constantCoeff_discrUnit`), hence is a unit of `ℤ⟦X⟧`
  (`isUnit_discrUnit`), so `j(q)` is the evaluation of an integer Laurent series.

The expansions rest on the finite-tail bound `le_orderTop_tateSum_sub_sum` and on
`five_nsmul_le_orderTop_tateSum_sub`,
`s_j(q) = q + (1 + 2^j)q² + (1 + 3^j)q³ + (1 + 2^j + 4^j)q⁴ + O(q⁵)` for every `j`.
Congruences modulo `q^N` are membership in the ideal `orderIdeal (N • v(q))` of the
nonnegative-order subring; the polynomial algebra is done once, in an arbitrary commutative
ring, by `formulas_mod_two` and `formulas_mod_five`.

Hypotheses. `(12 : k) ≠ 0` replaces characteristic zero: in characteristic `2` or `3`,
`tateA6` is Lean's junk value. Writing `v(q) = α` with `α : Γ` encodes `q ≠ 0`, which the
source's `v(q) = α > 0` includes. The `j` statements take an instance
`[(tateCurve q).IsElliptic]`, which `isElliptic_tateCurve` supplies; the class is a
proposition, so `j` does not depend on the instance.

Pending: the product formula `Δ(q) = q ∏_{n ≥ 1} (1 - qⁿ)²⁴` of `tate:eq:Delta`. By
`tateCurve_Δ_eq_heval` it reduces, given the compatibility of `PowerSeries.heval q` with the
infinite product (the evaluation of the formal product `X ∏ (1 - Xⁿ)²⁴` is the Hahn product
`q ∏ (1 - qⁿ)²⁴`, for example via `Surreal.HahnSeries.InfiniteProducts`), to the classical
identity `discrFormula a4Series a6Series = X ∏ (1 - Xⁿ)²⁴` in `ℤ⟦X⟧`. Neither step is proved
here: no compatibility of `heval` with infinite products is used.

Not a clause of the source: the displayed terms of `tate:eq:j` and its Laurent-series clause
are proved above at the Hahn level. The coefficient identity
`jSeries = 1 + 744X + 196884X² + 21493760X³ + ⋯` in `ℤ⟦X⟧` would be an optional
strengthening and is not proved here.
-/

namespace Surreal.TateDiscriminant

open _root_.HahnSeries Surreal.TateNode Surreal.HahnSeries

noncomputable section

/-! ### Integrality of the coefficients of `a₆` -/

/-- `12 ∣ 5m³ + 7m⁵` for every integer `m`. -/
theorem twelve_dvd_five_mul_pow_three_add_seven_mul_pow_five (m : ℤ) :
    (12 : ℤ) ∣ 5 * m ^ 3 + 7 * m ^ 5 := by
  have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have hm := h m
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp (by push_cast; exact hm)

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-! ### Order bounds for the Lambert terms -/

/-- The finite geometric identity behind the Lambert terms. -/
theorem sub_sum_pow_mul_one_sub {R : Type*} [CommRing R] (x : R) (K : ℕ) :
    x - (∑ i ∈ Finset.range K, x ^ (i + 1)) * (1 - x) = x ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    linear_combination ih

theorem addVal_one_sub {x : k⟦Γ⟧} (hx : 0 < x.orderTop) : addVal Γ k (1 - x) = 0 := by
  rw [AddValuation.map_sub_eq_of_lt_left _
    (by rw [AddValuation.map_one, addVal_apply]; exact hx), AddValuation.map_one]

theorem one_sub_ne_zero {x : k⟦Γ⟧} (hx : 0 < x.orderTop) : 1 - x ≠ 0 := by
  intro h
  have h1 := addVal_one_sub hx
  rw [h, AddValuation.map_zero] at h1
  exact WithTop.top_ne_zero h1

theorem orderTop_div_one_sub {x : k⟦Γ⟧} (hx : 0 < x.orderTop) (y : k⟦Γ⟧) :
    (y / (1 - x)).orderTop = y.orderTop := by
  rw [← addVal_apply, AddValuation.map_div, addVal_one_sub hx, sub_zero, addVal_apply]

theorem orderTop_pow_pos {x : k⟦Γ⟧} (hx : 0 < x.orderTop) {m : ℕ} (hm : m ≠ 0) :
    0 < (x ^ m).orderTop := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [pow_succ', ← addVal_apply, AddValuation.map_mul, AddValuation.map_pow, addVal_apply]
  exact add_pos_of_pos_of_nonneg hx (nsmul_nonneg hx.le m)

theorem orderTop_pow (x : k⟦Γ⟧) (m : ℕ) : (x ^ m).orderTop = m • x.orderTop := by
  rw [← addVal_apply, AddValuation.map_pow, addVal_apply]

/-- `x/(1 - x) - (x + ⋯ + x^K) = x^(K+1)/(1 - x)` for `v(x) > 0`. -/
theorem div_one_sub_sub_sum {x : k⟦Γ⟧} (hx : 0 < x.orderTop) (K : ℕ) :
    x / (1 - x) - ∑ i ∈ Finset.range K, x ^ (i + 1) = x ^ (K + 1) / (1 - x) := by
  have h := one_sub_ne_zero hx
  rw [eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  exact sub_sum_pow_mul_one_sub x K

/-- The `n`-th Lambert term `(n+1)^j q^(n+1)/(1 - q^(n+1))` has order at least
`(n+1) v(q)`. -/
theorem le_orderTop_tateFamily (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) (n : ℕ) :
    (n + 1) • q.orderTop ≤ (tateFamily j q n).orderTop := by
  rw [tateFamily_apply_of_pos j hq]
  refine le_trans ?_ (not_lt.mp (orderTop_smul_not_lt _ _))
  rw [orderTop_div_one_sub (orderTop_pow_pos hq n.succ_ne_zero), orderTop_pow]

/-- Finite-tail bound for the Tate sums: omitting the Lambert terms with index `n > N`
leaves an error of order at least `(N+1) v(q)`. -/
theorem le_orderTop_tateSum_sub_sum (j N : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    (N + 1) • q.orderTop ≤
      (tateSum j q - ∑ n ∈ Finset.range N, tateFamily j q n).orderTop := by
  refine le_orderTop_iff_forall.mpr fun g hg => ?_
  rw [coeff_sub, tateSum, SummableFamily.coeff_hsum, coeff_sum, sub_eq_zero]
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hN
  refine hn (coeff_eq_zero_of_lt_orderTop (hg.trans_le ?_))
  exact le_trans (nsmul_le_nsmul_left hq.le (by omega)) (le_orderTop_tateFamily j hq n)

/-- `v(s_j(q)) ≥ v(q)`. -/
theorem le_orderTop_tateSum (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    q.orderTop ≤ (tateSum j q).orderTop := by
  simpa using le_orderTop_tateSum_sub_sum j 0 hq

theorem tateFamily_zero (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    tateFamily j q 0 = q / (1 - q) := by
  rw [tateFamily_apply_of_pos j hq]
  simp

/-- `tate:prop:discriminant`, first-order term of the Tate sums:
`s_j(q) = q + O(q²)`, i.e. `v(s_j(q) - q) ≥ 2 v(q)`. -/
theorem two_nsmul_le_orderTop_tateSum_sub (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    2 • q.orderTop ≤ (tateSum j q - q).orderTop := by
  have h1 := le_orderTop_tateSum_sub_sum j 1 hq
  rw [Finset.sum_range_one, tateFamily_zero j hq, one_add_one_eq_two] at h1
  have h2 : 2 • q.orderTop ≤ (q / (1 - q) - q).orderTop := by
    have h := div_one_sub_sub_sum hq 1
    rw [Finset.sum_range_one, zero_add, pow_one] at h
    rw [h, orderTop_div_one_sub hq, orderTop_pow]
  have h3 : tateSum j q - q = (tateSum j q - q / (1 - q)) + (q / (1 - q) - q) := by ring
  rw [h3]
  exact (le_min h1 h2).trans min_orderTop_le_orderTop_add

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem le_orderTop_add {γ : WithTop Γ} {x y : k⟦Γ⟧} (hx : γ ≤ x.orderTop)
    (hy : γ ≤ y.orderTop) : γ ≤ (x + y).orderTop :=
  (le_min hx hy).trans min_orderTop_le_orderTop_add

theorem orderTop_natCast_nonneg (c : ℕ) : 0 ≤ ((c : k⟦Γ⟧)).orderTop := by
  rw [← map_natCast (C : k →+* k⟦Γ⟧) c, C_apply]
  exact orderTop_single_le

theorem le_orderTop_natCast_mul (c : ℕ) (x : k⟦Γ⟧) :
    x.orderTop ≤ ((c : k⟦Γ⟧) * x).orderTop := by
  rw [orderTop_mul]
  exact le_add_of_nonneg_left (orderTop_natCast_nonneg c)

theorem tateFamily_eq (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) (n : ℕ) :
    tateFamily j q n = (((n + 1) ^ j : ℕ) : k⟦Γ⟧) * (q ^ (n + 1) / (1 - q ^ (n + 1))) := by
  rw [tateFamily_apply_of_pos j hq, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/-- Truncating one Lambert term `c q^m/(1 - q^m) = c (q^m + q^(2m) + ⋯)` after `K` terms
leaves an error of order at least `m (K+1) v(q)`. -/
theorem le_orderTop_lambert_sub {q : k⟦Γ⟧} (hq : 0 < q.orderTop) (c m K : ℕ) (hm : m ≠ 0) :
    (m * (K + 1)) • q.orderTop ≤ ((c : k⟦Γ⟧) * (q ^ m / (1 - q ^ m)) -
      (c : k⟦Γ⟧) * ∑ i ∈ Finset.range K, (q ^ m) ^ (i + 1)).orderTop := by
  rw [← mul_sub, div_one_sub_sub_sum (orderTop_pow_pos hq hm) K]
  refine le_trans ?_ (le_orderTop_natCast_mul c _)
  rw [orderTop_div_one_sub (orderTop_pow_pos hq hm), orderTop_pow, orderTop_pow, mul_nsmul]

/-- `tate:prop:discriminant`, the Tate sums to fifth order:
`s_j(q) = q + (1 + 2^j) q² + (1 + 3^j) q³ + (1 + 2^j + 4^j) q⁴ + O(q⁵)`, the coefficients
being the divisor sums `σ_j(1), …, σ_j(4)`. -/
theorem five_nsmul_le_orderTop_tateSum_sub (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    5 • q.orderTop ≤ (tateSum j q - (q + (1 + 2 ^ j) * q ^ 2 + (1 + 3 ^ j) * q ^ 3 +
      (1 + 2 ^ j + 4 ^ j) * q ^ 4)).orderTop := by
  have hE := le_orderTop_tateSum_sub_sum j 4 hq
  have h0 := le_orderTop_lambert_sub hq 1 1 4 one_ne_zero
  have h1 := le_orderTop_lambert_sub hq (2 ^ j) 2 2 two_ne_zero
  have h2 := le_orderTop_lambert_sub hq (3 ^ j) 3 1 three_ne_zero
  have h3 := le_orderTop_lambert_sub hq (4 ^ j) 4 1 four_ne_zero
  have hle : ∀ m : ℕ, 5 ≤ m → 5 • q.orderTop ≤ m • q.orderTop :=
    fun m hm => nsmul_le_nsmul_left hq.le hm
  have key : tateSum j q - (q + (1 + 2 ^ j) * q ^ 2 + (1 + 3 ^ j) * q ^ 3 +
      (1 + 2 ^ j + 4 ^ j) * q ^ 4) =
      (tateSum j q - ∑ n ∈ Finset.range 4, tateFamily j q n) +
      (((1 : ℕ) : k⟦Γ⟧) * (q ^ 1 / (1 - q ^ 1)) -
        ((1 : ℕ) : k⟦Γ⟧) * ∑ i ∈ Finset.range 4, (q ^ 1) ^ (i + 1)) +
      ((((2 ^ j : ℕ)) : k⟦Γ⟧) * (q ^ 2 / (1 - q ^ 2)) -
        ((2 ^ j : ℕ) : k⟦Γ⟧) * ∑ i ∈ Finset.range 2, (q ^ 2) ^ (i + 1)) +
      ((((3 ^ j : ℕ)) : k⟦Γ⟧) * (q ^ 3 / (1 - q ^ 3)) -
        ((3 ^ j : ℕ) : k⟦Γ⟧) * ∑ i ∈ Finset.range 1, (q ^ 3) ^ (i + 1)) +
      ((((4 ^ j : ℕ)) : k⟦Γ⟧) * (q ^ 4 / (1 - q ^ 4)) -
        ((4 ^ j : ℕ) : k⟦Γ⟧) * ∑ i ∈ Finset.range 1, (q ^ 4) ^ (i + 1)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, tateFamily_eq j hq, zero_add,
      Nat.reduceAdd, one_pow]
    push_cast
    ring
  rw [key]
  refine le_orderTop_add (le_orderTop_add (le_orderTop_add (le_orderTop_add ?_ ?_) ?_) ?_) ?_
  · exact hE
  · exact (hle _ (by norm_num)).trans h0
  · exact (hle _ (by norm_num)).trans h1
  · exact (hle _ (by norm_num)).trans h2
  · exact (hle _ (by norm_num)).trans h3

/-! ### The Tate polynomials over an arbitrary commutative ring -/

section Formulas

variable {A : Type*} [CommRing A]

/-- `a₆ = -w (5 s₃ + 7 s₅)`, where `w` plays the role of `1/12`. -/
def a6Formula (s3 s5 w : A) : A := -(w * (5 * s3 + 7 * s5))

/-- The discriminant `-a₆ + a₄² - 64 a₄³ - 432 a₆² + 72 a₄ a₆` of `y² + xy = x³ + a₄x + a₆`. -/
def discrFormula (a4 a6 : A) : A := -a6 + a4 ^ 2 - 64 * a4 ^ 3 - 432 * a6 ^ 2 + 72 * a4 * a6

/-- The invariant `c₄ = 1 - 48 a₄` of `y² + xy = x³ + a₄x + a₆`. -/
def c4Formula (a4 : A) : A := 1 - 48 * a4

/-- The Tate polynomials modulo `t²`: if `s₃ ≡ s₅ ≡ t` and `12 w ≡ 1`, then `a₆ ≡ -t`,
`Δ ≡ t` and `t c₄³ ≡ Δ`. -/
theorem formulas_mod_two (I : Ideal A) {t s3 s5 w : A} (ht : t ^ 2 ∈ I) (h3 : s3 - t ∈ I)
    (h5 : s5 - t ∈ I) (hw : w * 12 - 1 ∈ I) :
    a6Formula s3 s5 w - -t ∈ I ∧ discrFormula (-5 * s3) (a6Formula s3 s5 w) - t ∈ I ∧
      t * c4Formula (-5 * s3) ^ 3 - discrFormula (-5 * s3) (a6Formula s3 s5 w) ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow] at ht
  rw [← Ideal.Quotient.eq] at h3 h5
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_ofNat, map_one, sub_eq_zero] at hw
  simp only [← Ideal.Quotient.eq, a6Formula, discrFormula, c4Formula, map_add, map_sub,
    map_mul, map_neg, map_pow, map_ofNat, map_one, h3, h5]
  set T := Ideal.Quotient.mk I t
  set W := Ideal.Quotient.mk I w
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-T) * hw
  · linear_combination T * hw + (25 + 8000 * T - 62208 * W ^ 2 + 4320 * W) * ht
  · linear_combination (720 + 172800 * T + 13824000 * T ^ 2 -
      (25 + 8000 * T - 62208 * W ^ 2 + 4320 * W)) * ht - T * hw

/-- The Tate polynomials modulo `t⁵`: if `s₃ ≡ t + 9t² + 28t³ + 73t⁴`,
`s₅ ≡ t + 33t² + 244t³ + 1057t⁴` and `12 w ≡ 1`, then
`Δ ≡ t - 24t² + 252t³ - 1472t⁴` and `t c₄³ ≡ (1 + 744t + 196884t² + 21493760t³) Δ`. -/
theorem formulas_mod_five (I : Ideal A) {t s3 s5 w : A} (ht : t ^ 5 ∈ I)
    (h3 : s3 - (t + 9 * t ^ 2 + 28 * t ^ 3 + 73 * t ^ 4) ∈ I)
    (h5 : s5 - (t + 33 * t ^ 2 + 244 * t ^ 3 + 1057 * t ^ 4) ∈ I) (hw : w * 12 - 1 ∈ I) :
    discrFormula (-5 * s3) (a6Formula s3 s5 w) -
        (t - 24 * t ^ 2 + 252 * t ^ 3 - 1472 * t ^ 4) ∈ I ∧
      t * c4Formula (-5 * s3) ^ 3 - (1 + 744 * t + 196884 * t ^ 2 + 21493760 * t ^ 3) *
        discrFormula (-5 * s3) (a6Formula s3 s5 w) ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow] at ht
  rw [← Ideal.Quotient.eq] at h3 h5
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_ofNat, map_one, sub_eq_zero] at hw
  simp only [map_add, map_mul, map_pow, map_ofNat] at h3 h5
  set T := Ideal.Quotient.mk I t
  set W := Ideal.Quotient.mk I w
  have ha6 : Ideal.Quotient.mk I (a6Formula s3 s5 w) =
      -(T + 23 * T ^ 2 + 154 * T ^ 3 + 647 * T ^ 4) := by
    simp only [a6Formula, map_neg, map_mul, map_add, map_ofNat, h3, h5]
    linear_combination (-(T + 23 * T ^ 2 + 154 * T ^ 3 + 647 * T ^ 4)) * hw
  have hΔ : Ideal.Quotient.mk I (discrFormula (-5 * s3) (a6Formula s3 s5 w)) =
      T - 24 * T ^ 2 + 252 * T ^ 3 - 1472 * T ^ 4 := by
    simp only [discrFormula, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, h3, ha6]
    linear_combination (3112136000 * T ^ 7 + 3581088000 * T ^ 6 + 2524632000 * T ^ 5 +
      1186520000 * T ^ 4 + 245665297 * T ^ 3 + 29367848 * T ^ 2 + 882994 * T + 2954) * ht
  refine ⟨?_, ?_⟩
  · rw [← Ideal.Quotient.eq]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hΔ]
    rfl
  · rw [← Ideal.Quotient.eq]
    simp only [c4Formula, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, h3,
      hΔ]
    linear_combination (5377771008000 * T ^ 8 + 6188120064000 * T ^ 7 +
      4362564096000 * T ^ 6 + 2050306560000 * T ^ 5 + 708308755200 * T ^ 4 +
      181773158400 * T ^ 3 + 66008389120 * T ^ 2 - 493846272 * T + 864304800) * ht

end Formulas

/-! ### Congruences modulo powers of `q` -/

/-- The ideal of the nonnegative-order subring formed by the series of order at least `γ`.
A congruence modulo `q^N` is membership in `orderIdeal (N • v(q))`. -/
def orderIdeal (γ : WithTop Γ) : Ideal (nonnegativeSubring Γ k) where
  carrier := {x | γ ≤ (x : k⟦Γ⟧).orderTop}
  add_mem' hx hy := le_orderTop_add hx hy
  zero_mem' := by simp
  smul_mem' c x hx := by
    change γ ≤ ((c : k⟦Γ⟧) * x).orderTop
    rw [orderTop_mul]
    exact hx.trans (le_add_of_nonneg_left ((mem_nonnegativeSubring _).mp c.2))

theorem sub_mem_orderIdeal_iff {γ : WithTop Γ} (x y : nonnegativeSubring Γ k) :
    x - y ∈ orderIdeal γ ↔ γ ≤ ((x : k⟦Γ⟧) - y).orderTop :=
  Iff.rfl

/-- A Hahn series of nonnegative order as an element of the nonnegative-order subring. -/
def toO (x : k⟦Γ⟧) (hx : 0 ≤ x.orderTop) : nonnegativeSubring Γ k :=
  ⟨x, (mem_nonnegativeSubring x).mpr hx⟩

@[simp]
theorem coe_toO (x : k⟦Γ⟧) (hx : 0 ≤ x.orderTop) : (toO x hx : k⟦Γ⟧) = x := rfl

theorem pow_mem_orderIdeal {q : k⟦Γ⟧} (hq : 0 ≤ q.orderTop) (N : ℕ) :
    toO q hq ^ N ∈ orderIdeal (N • q.orderTop) := by
  change N • q.orderTop ≤ ((toO q hq ^ N : nonnegativeSubring Γ k) : k⟦Γ⟧).orderTop
  rw [SubmonoidClass.coe_pow, coe_toO, orderTop_pow]

/-- `s_j(q)` in the nonnegative-order subring. -/
def sumO (j : ℕ) (q : k⟦Γ⟧) : nonnegativeSubring Γ k :=
  toO (tateSum j q) (orderTop_tateSum_pos j q).le

/-- `1/12` in the nonnegative-order subring. -/
def twelveInvO : nonnegativeSubring Γ k :=
  toO (C (12 : k)⁻¹) (by rw [C_apply]; exact orderTop_single_le)

theorem twelveInvO_mul_sub_one_mem (h12 : (12 : k) ≠ 0) (γ : WithTop Γ) :
    (twelveInvO : nonnegativeSubring Γ k) * 12 - 1 ∈ orderIdeal γ := by
  have h : (twelveInvO : nonnegativeSubring Γ k) * 12 = 1 := by
    apply Subtype.ext
    change C (12 : k)⁻¹ * 12 = 1
    rw [← map_ofNat (C : k →+* k⟦Γ⟧) 12, ← map_mul, inv_mul_cancel₀ h12, map_one]
  rw [h, sub_self]
  exact Ideal.zero_mem _

/-- The discriminant of `E_q : y² + xy = x³ + a₄x + a₆` (`a₁ = 1`, `a₂ = a₃ = 0`), from
`b₂ = 1`, `b₄ = 2a₄`, `b₆ = 4a₆`, `b₈ = a₆ - a₄²`. -/
theorem tateCurve_Δ (q : k⟦Γ⟧) : (tateCurve q).Δ = -tateA6 q + tateA4 q ^ 2 -
    64 * tateA4 q ^ 3 - 432 * tateA6 q ^ 2 + 72 * tateA4 q * tateA6 q := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, tateCurve]
  ring

/-- `c₄ = 1 - 48 a₄` for `E_q`. -/
theorem tateCurve_c₄ (q : k⟦Γ⟧) : (tateCurve q).c₄ = 1 - 48 * tateA4 q := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tateCurve]
  ring

/-- `a₆(q)` through the generic formula, with `w = 1/12`. -/
theorem a6Formula_tate (q : k⟦Γ⟧) :
    a6Formula (tateSum 3 q) (tateSum 5 q) (C (12 : k)⁻¹) = tateA6 q := by
  rw [a6Formula, tateA6, map_inv₀, map_ofNat]
  ring

/-- `Δ(q)` through the generic formula. -/
theorem discrFormula_tate (q : k⟦Γ⟧) :
    discrFormula (-5 * tateSum 3 q) (a6Formula (tateSum 3 q) (tateSum 5 q) (C (12 : k)⁻¹)) =
      (tateCurve q).Δ := by
  rw [a6Formula_tate, tateCurve_Δ, discrFormula, tateA4]

/-- `c₄(q)` through the generic formula. -/
theorem c4Formula_tate (q : k⟦Γ⟧) : c4Formula (-5 * tateSum 3 q) = (tateCurve q).c₄ := by
  rw [tateCurve_c₄, c4Formula, tateA4]

/-! ### The discriminant: `Δ(q) = q + O(q²)` -/

/-- The congruences modulo `q²`: `a₆(q) ≡ -q`, `Δ(q) ≡ q` and `q c₄(q)³ ≡ Δ(q)`. -/
theorem mod_two (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    2 • q.orderTop ≤ (tateA6 q + q).orderTop ∧
      2 • q.orderTop ≤ ((tateCurve q).Δ - q).orderTop ∧
      2 • q.orderTop ≤ (q * (tateCurve q).c₄ ^ 3 - (tateCurve q).Δ).orderTop := by
  have ht := pow_mem_orderIdeal (k := k) hq.le 2
  have h3 := (sub_mem_orderIdeal_iff (γ := 2 • q.orderTop) (sumO 3 q) (toO q hq.le)).mpr
    (two_nsmul_le_orderTop_tateSum_sub 3 hq)
  have h5 := (sub_mem_orderIdeal_iff (γ := 2 • q.orderTop) (sumO 5 q) (toO q hq.le)).mpr
    (two_nsmul_le_orderTop_tateSum_sub 5 hq)
  obtain ⟨e1, e2, e3⟩ := formulas_mod_two _ ht h3 h5 (twelveInvO_mul_sub_one_mem h12 _)
  rw [sub_mem_orderIdeal_iff] at e1 e2 e3
  change 2 • q.orderTop ≤
    (a6Formula (tateSum 3 q) (tateSum 5 q) (C (12 : k)⁻¹) - -q).orderTop at e1
  change 2 • q.orderTop ≤ (discrFormula (-5 * tateSum 3 q)
    (a6Formula (tateSum 3 q) (tateSum 5 q) (C (12 : k)⁻¹)) - q).orderTop at e2
  change 2 • q.orderTop ≤ (q * c4Formula (-5 * tateSum 3 q) ^ 3 - discrFormula
    (-5 * tateSum 3 q) (a6Formula (tateSum 3 q) (tateSum 5 q) (C (12 : k)⁻¹))).orderTop at e3
  rw [a6Formula_tate, sub_neg_eq_add] at e1
  rw [discrFormula_tate] at e2
  rw [c4Formula_tate, discrFormula_tate] at e3
  exact ⟨e1, e2, e3⟩

/-- `tate:prop:discriminant`, proof step: `a₆(q) = -q + O(q²)`. -/
theorem two_nsmul_le_orderTop_tateA6_add (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧}
    (hq : 0 < q.orderTop) : 2 • q.orderTop ≤ (tateA6 q + q).orderTop :=
  (mod_two h12 hq).1

/-- `tate:prop:discriminant`, proof step: `Δ(q) = q + O(q²)`, i.e.
`v(Δ(q) - q) ≥ 2 v(q)`. -/
theorem two_nsmul_le_orderTop_tateCurve_Δ_sub (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧}
    (hq : 0 < q.orderTop) : 2 • q.orderTop ≤ ((tateCurve q).Δ - q).orderTop :=
  (mod_two h12 hq).2.1

theorem orderTop_lt_two_nsmul {q : k⟦Γ⟧} {α : Γ} (hα : q.orderTop = α) (hα0 : 0 < α) :
    q.orderTop < 2 • q.orderTop := by
  rw [hα, ← WithTop.coe_nsmul, WithTop.coe_lt_coe, two_nsmul]
  exact lt_add_of_pos_right α hα0

omit [IsOrderedAddMonoid Γ] in
theorem orderTop_pos_of_eq {q : k⟦Γ⟧} {α : Γ} (hα : q.orderTop = α) (hα0 : 0 < α) :
    0 < q.orderTop := by
  rw [hα]
  exact_mod_cast hα0

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem ne_zero_of_orderTop_eq {q : k⟦Γ⟧} {α : Γ} (hα : q.orderTop = α) : q ≠ 0 := by
  rintro rfl
  simp at hα

/-- `tate:eq:Delta`, valuation clause: `v(Δ(q)) = α`. -/
theorem orderTop_tateCurve_Δ (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) : (tateCurve q).Δ.orderTop = α := by
  have hlt := (orderTop_lt_two_nsmul hα hα0).trans_le
    (two_nsmul_le_orderTop_tateCurve_Δ_sub h12 (orderTop_pos_of_eq hα hα0))
  have e : (tateCurve q).Δ = q + ((tateCurve q).Δ - q) := by ring
  rw [e, orderTop_add_eq_left hlt, hα]

/-- The leading coefficient of `Δ(q)` is that of `q`. -/
theorem leadingCoeff_tateCurve_Δ (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) : (tateCurve q).Δ.leadingCoeff = q.leadingCoeff := by
  have hlt := (orderTop_lt_two_nsmul hα hα0).trans_le
    (two_nsmul_le_orderTop_tateCurve_Δ_sub h12 (orderTop_pos_of_eq hα hα0))
  have e : (tateCurve q).Δ = q + ((tateCurve q).Δ - q) := by ring
  rw [e, leadingCoeff_add_eq_left hlt]

theorem tateCurve_Δ_ne_zero (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) : (tateCurve q).Δ ≠ 0 :=
  ne_zero_of_orderTop_eq (orderTop_tateCurve_Δ h12 hα hα0)

/-- `tate:prop:discriminant`, last clause: `E_q` is an elliptic curve over `K_Γ`. -/
theorem isElliptic_tateCurve (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) : (tateCurve q).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (tateCurve_Δ_ne_zero h12 hα hα0)⟩

/-- `tate:prop:discriminant`, last clause: every affine point of `E_q` is nonsingular. -/
theorem tateCurve_equation_iff_nonsingular (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) {x y : k⟦Γ⟧} :
    (tateCurve q).toAffine.Equation x y ↔ (tateCurve q).toAffine.Nonsingular x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (tateCurve_Δ_ne_zero h12 hα hα0)

/-! ### The modular invariant: valuation and leading term -/

/-- `j = c₄³/Δ`. -/
theorem tateCurve_j (q : k⟦Γ⟧) [(tateCurve q).IsElliptic] :
    (tateCurve q).j = (tateCurve q).c₄ ^ 3 / (tateCurve q).Δ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', div_eq_inv_mul]

theorem le_orderTop_div {x y : k⟦Γ⟧} {a b : Γ} (hx : (a : WithTop Γ) ≤ x.orderTop)
    (hy : y.orderTop = b) : ((a - b : Γ) : WithTop Γ) ≤ (x / y).orderTop := by
  rw [← addVal_apply, AddValuation.map_div, addVal_apply, addVal_apply, hy,
    WithTop.LinearOrderedAddCommGroup.coe_sub, sub_eq_add_neg, sub_eq_add_neg]
  exact add_le_add hx le_rfl

/-- `tate:eq:j`, leading term: `j(q) q = 1 + O(q)`, i.e. `v(j(q) q - 1) ≥ α`. -/
theorem le_orderTop_tateCurve_j_mul_sub_one (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) [(tateCurve q).IsElliptic] :
    (α : WithTop Γ) ≤ ((tateCurve q).j * q - 1).orderTop := by
  have hΔ0 := tateCurve_Δ_ne_zero h12 hα hα0
  have e : (tateCurve q).j * q - 1 =
      (q * (tateCurve q).c₄ ^ 3 - (tateCurve q).Δ) / (tateCurve q).Δ := by
    rw [tateCurve_j, eq_div_iff hΔ0, sub_mul, one_mul, mul_right_comm, div_mul_cancel₀ _ hΔ0]
    ring
  have h2 := (mod_two h12 (orderTop_pos_of_eq hα hα0)).2.2
  rw [hα, ← WithTop.coe_nsmul] at h2
  have h := le_orderTop_div h2 (orderTop_tateCurve_Δ h12 hα hα0)
  rwa [two_nsmul, add_sub_cancel_right, ← e] at h

/-- `tate:eq:j`, valuation clause: `v(j(q)) = -α`; the leading coefficient of `j(q)` is the
inverse of that of `q`, so the leading term of `j(q)` is that of `q⁻¹`. -/
theorem orderTop_tateCurve_j (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) [(tateCurve q).IsElliptic] :
    (tateCurve q).j.orderTop = ((-α : Γ) : WithTop Γ) ∧
      (tateCurve q).j.leadingCoeff = q.leadingCoeff⁻¹ := by
  have hpos : 0 < ((tateCurve q).j * q - 1).orderTop :=
    lt_of_lt_of_le (by exact_mod_cast hα0) (le_orderTop_tateCurve_j_mul_sub_one h12 hα hα0)
  obtain ⟨h1, h2⟩ := (orderTop_self_sub_one_pos_iff _).mp hpos
  refine ⟨?_, ?_⟩
  · have hq0 := ne_zero_of_orderTop_eq hα
    rw [← mul_inv_cancel_right₀ hq0 (tateCurve q).j, orderTop_mul, h1, zero_add,
      ← addVal_apply, AddValuation.map_inv, addVal_apply, hα,
      WithTop.LinearOrderedAddCommGroup.coe_neg]
  · rw [leadingCoeff_mul] at h2
    exact eq_inv_of_mul_eq_one_left h2

/-! ### Expansions of `Δ(q)` and `j(q)` to higher order -/

/-- The congruences modulo `q⁵`: `Δ(q) ≡ q - 24q² + 252q³ - 1472q⁴` and
`q c₄(q)³ ≡ (1 + 744q + 196884q² + 21493760q³) Δ(q)`. -/
theorem mod_five (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    5 • q.orderTop ≤
        ((tateCurve q).Δ - (q - 24 * q ^ 2 + 252 * q ^ 3 - 1472 * q ^ 4)).orderTop ∧
      5 • q.orderTop ≤ (q * (tateCurve q).c₄ ^ 3 -
        (1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3) * (tateCurve q).Δ).orderTop := by
  have hs3 : 5 • q.orderTop ≤
      (tateSum 3 q - (q + 9 * q ^ 2 + 28 * q ^ 3 + 73 * q ^ 4)).orderTop := by
    have h := five_nsmul_le_orderTop_tateSum_sub 3 hq
    norm_num at h
    exact h
  have hs5 : 5 • q.orderTop ≤
      (tateSum 5 q - (q + 33 * q ^ 2 + 244 * q ^ 3 + 1057 * q ^ 4)).orderTop := by
    have h := five_nsmul_le_orderTop_tateSum_sub 5 hq
    norm_num at h
    exact h
  obtain ⟨e1, e2⟩ := formulas_mod_five (orderIdeal (k := k) (5 • q.orderTop))
    (t := toO q hq.le) (s3 := sumO 3 q) (s5 := sumO 5 q) (w := twelveInvO)
    (pow_mem_orderIdeal hq.le 5) ((sub_mem_orderIdeal_iff _ _).mpr hs3)
    ((sub_mem_orderIdeal_iff _ _).mpr hs5) (twelveInvO_mul_sub_one_mem h12 _)
  rw [sub_mem_orderIdeal_iff] at e1 e2
  change 5 • q.orderTop ≤ (discrFormula (-5 * tateSum 3 q)
    (a6Formula (tateSum 3 q) (tateSum 5 q) (C (12 : k)⁻¹)) -
      (q - 24 * q ^ 2 + 252 * q ^ 3 - 1472 * q ^ 4)).orderTop at e1
  change 5 • q.orderTop ≤ (q * c4Formula (-5 * tateSum 3 q) ^ 3 -
    (1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3) * discrFormula (-5 * tateSum 3 q)
      (a6Formula (tateSum 3 q) (tateSum 5 q) (C (12 : k)⁻¹))).orderTop at e2
  rw [discrFormula_tate] at e1
  rw [c4Formula_tate, discrFormula_tate] at e2
  exact ⟨e1, e2⟩

/-- `tate:eq:Delta` to fifth order: `Δ(q) = q - 24q² + 252q³ - 1472q⁴ + O(q⁵)`. The four
coefficients are those of `q ∏ (1 - qⁿ)²⁴` (a numerical remark; the product formula itself is
pending). -/
theorem five_nsmul_le_orderTop_tateCurve_Δ_sub (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧}
    (hq : 0 < q.orderTop) :
    5 • q.orderTop ≤
      ((tateCurve q).Δ - (q - 24 * q ^ 2 + 252 * q ^ 3 - 1472 * q ^ 4)).orderTop :=
  (mod_five h12 hq).1

/-- `tate:eq:j` to the displayed order:
`j(q) = q⁻¹ + 744 + 196884q + 21493760q² + O(q³)`, i.e. the difference has valuation at
least `3α`. -/
theorem le_orderTop_tateCurve_j_sub (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) [(tateCurve q).IsElliptic] :
    ((3 • α : Γ) : WithTop Γ) ≤
      ((tateCurve q).j - (q⁻¹ + 744 + 196884 * q + 21493760 * q ^ 2)).orderTop := by
  have hq0 := ne_zero_of_orderTop_eq hα
  have hΔ0 := tateCurve_Δ_ne_zero h12 hα hα0
  have e : (tateCurve q).j - (q⁻¹ + 744 + 196884 * q + 21493760 * q ^ 2) =
      (q * (tateCurve q).c₄ ^ 3 - (1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3) *
        (tateCurve q).Δ) / (q * (tateCurve q).Δ) := by
    rw [tateCurve_j, eq_div_iff (mul_ne_zero hq0 hΔ0)]
    linear_combination q * div_mul_cancel₀ ((tateCurve q).c₄ ^ 3) hΔ0 -
      (tateCurve q).Δ * inv_mul_cancel₀ hq0
  have h5 := (mod_five h12 (orderTop_pos_of_eq hα hα0)).2
  rw [hα, ← WithTop.coe_nsmul] at h5
  have hden : (q * (tateCurve q).Δ).orderTop = ((2 • α : Γ) : WithTop Γ) := by
    rw [orderTop_mul, hα, orderTop_tateCurve_Δ h12 hα hα0, two_nsmul, WithTop.coe_add]
  have h := le_orderTop_div h5 hden
  rw [← e] at h
  have e3 : (5 • α - 2 • α : Γ) = 3 • α := by abel
  rwa [e3] at h

/-! ### The coefficients as Hahn evaluations of integer power series -/

/-- The integer power series `∑_{N ≥ 1} σ_j(N) X^N`. -/
def lambertSeries (j : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun N => ((ArithmeticFunction.sigma j N : ℕ) : ℤ)

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- The Hahn sum of a fiber of a summable family that vanishes on the fiber off a finite set
`t` contained in it is the finite sum over `t`. -/
theorem hsum_restrict_eq_sum {ι : Type*} (s : SummableFamily Γ k ι) (S : Set ι) (t : Finset ι)
    (hts : ∀ i ∈ t, i ∈ S) (hz : ∀ i ∈ S, i ∉ t → s i = 0) :
    (restrict s S).hsum = ∑ i ∈ t, s i := by
  ext g
  rw [SummableFamily.coeff_hsum, coeff_sum]
  simp only [restrict_apply]
  rw [finsum_set_coe_eq_finsum_mem S (f := fun i => (s i).coeff g)]
  refine finsum_cond_eq_sum_of_cond_iff _ fun {i} hi => ⟨fun hiS => ?_, hts i⟩
  by_contra hit
  exact hi (by rw [hz i hiS hit, coeff_zero])

/-- The Lambert double family `(n, m) ↦ (n+1)^j q^((n+1)(m+1))`. Its rows are the Lambert
terms of `s_j(q)`; grouping by `N = (n+1)(m+1)` gives `σ_j(N) q^N`. -/
def lambertDouble (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) : SummableFamily Γ k (ℕ × ℕ) where
  toFun p := (((p.1 + 1 : ℕ) : k) ^ j) • q ^ ((p.1 + 1) * (p.2 + 1))
  isPWO_iUnion_support' := by
    refine (SummableFamily.powers q).isPWO_iUnion_support.mono fun g hg => ?_
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hg
    refine Set.mem_iUnion.mpr ⟨(p.1 + 1) * (p.2 + 1), ?_⟩
    rw [SummableFamily.powers_of_orderTop_pos hq]
    exact support_smul_subset _ _ hp
  finite_co_support' g := by
    have hfin := (SummableFamily.powers q).finite_co_support g
    refine (hfin.preimage' (f := fun p : ℕ × ℕ => (p.1 + 1) * (p.2 + 1))
      fun N _ => ?_).subset fun p hp => ?_
    · refine ((Set.finite_Iic N).prod (Set.finite_Iic N)).subset fun p hp => ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
      simp only [Set.mem_prod, Set.mem_Iic]
      constructor <;> nlinarith
    · simp only [Set.mem_preimage, Function.mem_support,
        SummableFamily.powers_of_orderTop_pos hq]
      simp only [Set.mem_setOf_eq, coeff_smul, ne_eq] at hp
      exact right_ne_zero_of_smul hp

theorem lambertDouble_apply (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) (p : ℕ × ℕ) :
    lambertDouble j hq p = (((p.1 + 1 : ℕ) : k) ^ j) • q ^ ((p.1 + 1) * (p.2 + 1)) :=
  rfl

/-- The row `n` of the Lambert double family sums to the Lambert term
`(n+1)^j q^(n+1)/(1 - q^(n+1))`. -/
theorem hsum_lambertDouble_row (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) (n : ℕ) :
    (restrict (lambertDouble j hq) {p | p.1 = n}).hsum = tateFamily j q n := by
  let e : ℕ ≃ {p : ℕ × ℕ | p.1 = n} :=
    { toFun := fun m => ⟨(n, m), rfl⟩
      invFun := fun p => p.1.2
      left_inv := fun _ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext p.2.symm rfl) }
  have hF : restrict (lambertDouble j hq) {p | p.1 = n} =
      SummableFamily.Equiv e ((C (((n + 1 : ℕ) : k) ^ j) * q ^ (n + 1)) •
        SummableFamily.powers (q ^ (n + 1))) := by
    refine SummableFamily.ext fun p => ?_
    obtain ⟨⟨a, m⟩, ha⟩ := p
    simp only [Set.mem_setOf_eq] at ha
    subst ha
    rw [restrict_apply, SummableFamily.Equiv_toFun, SummableFamily.smul_apply,
      of_symm_smul_of_eq_mul,
      SummableFamily.powers_of_orderTop_pos (orderTop_pow_pos hq a.succ_ne_zero),
      lambertDouble_apply, ← C_mul_eq_smul]
    change C (((a + 1 : ℕ) : k) ^ j) * q ^ ((a + 1) * (m + 1)) =
      C (((a + 1 : ℕ) : k) ^ j) * q ^ (a + 1) * (q ^ (a + 1)) ^ m
    ring
  rw [hF, SummableFamily.hsum_equiv, SummableFamily.hsum_smul,
    geometric_hsum _ (orderTop_pow_pos hq n.succ_ne_zero), tateFamily_apply_of_pos j hq,
    ← C_mul_eq_smul, div_eq_mul_inv, mul_assoc]

/-- The terms of the Lambert double family with `(n+1)(m+1) = N` sum to `σ_j(N) q^N`. -/
theorem hsum_lambertDouble_fiber (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) (N : ℕ) :
    (restrict (lambertDouble j hq) {p | (p.1 + 1) * (p.2 + 1) = N}).hsum =
      ((ArithmeticFunction.sigma j N : ℕ) : k) • q ^ N := by
  have hmem : ∀ p ∈ N.divisorsAntidiagonal, 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 = N := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.one_le_iff_ne_zero.mpr ?_, hp.1⟩ <;>
      rintro h <;> simp only [h, zero_mul, mul_zero] at hp <;> exact hp.2 hp.1.symm
  rw [hsum_restrict_eq_sum _ _ (N.divisorsAntidiagonal.image fun p => (p.1 - 1, p.2 - 1))]
  · rw [Finset.sum_image]
    · calc ∑ p ∈ N.divisorsAntidiagonal, lambertDouble j hq (p.1 - 1, p.2 - 1)
          = ∑ p ∈ N.divisorsAntidiagonal, ((p.1 : k) ^ j) • q ^ N := by
            refine Finset.sum_congr rfl fun p hp => ?_
            obtain ⟨h1, h2, h3⟩ := hmem p hp
            rw [lambertDouble_apply]
            simp only [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2, h3]
        _ = ((ArithmeticFunction.sigma j N : ℕ) : k) • q ^ N := by
            rw [← Finset.sum_smul, ArithmeticFunction.sigma_apply,
              Nat.sum_divisorsAntidiagonal (fun a _ => (a : k) ^ j)]
            push_cast
            rfl
    · intro p hp p' hp' h
      obtain ⟨h1, h2, -⟩ := hmem p hp
      obtain ⟨h1', h2', -⟩ := hmem p' hp'
      simp only [Prod.mk.injEq] at h
      ext <;> omega
  · intro p hp
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨h1, h2, h3⟩ := hmem p' hp'
    change (p'.1 - 1 + 1) * (p'.2 - 1 + 1) = N
    rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2, h3]
  · intro p hp hpt
    exfalso
    apply hpt
    refine Finset.mem_image.mpr ⟨(p.1 + 1, p.2 + 1), ?_, by simp⟩
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨hp, ?_⟩
    rw [← show (p.1 + 1) * (p.2 + 1) = N from hp]
    positivity

/-- `tate:prop:discriminant`, first clause, for the Tate sums: `s_j(q)` is the Hahn
evaluation at `q` of the integer power series `∑ σ_j(N) X^N`. The proof regroups the
jointly summable Lambert double family in two ways. -/
theorem tateSum_eq_heval (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    tateSum j q = PowerSeries.heval q (PowerSeries.map (Int.castRingHom k) (lambertSeries j)) := by
  have h1 : regroup (lambertDouble j hq) Prod.fst = tateFamily j q :=
    SummableFamily.ext fun n => hsum_lambertDouble_row j hq n
  have h2 : regroup (lambertDouble j hq) (fun p => (p.1 + 1) * (p.2 + 1)) =
      SummableFamily.powerSeriesFamily q
        (PowerSeries.map (Int.castRingHom k) (lambertSeries j)) := by
    refine SummableFamily.ext fun N => ?_
    rw [regroup_apply]
    refine (hsum_lambertDouble_fiber j hq N).trans ?_
    rw [SummableFamily.powerSeriesFamily_of_orderTop_pos hq, PowerSeries.coeff_map,
      lambertSeries, PowerSeries.coeff_mk]
    simp
  rw [tateSum, ← h1, hsum_regroup,
    ← hsum_regroup (lambertDouble j hq) (fun p => (p.1 + 1) * (p.2 + 1)), h2,
    PowerSeries.heval_apply]

/-- The integer power series `-5 ∑ σ₃(N) X^N` of `a₄`. -/
def a4Series : PowerSeries ℤ := -5 * lambertSeries 3

/-- The integer power series of `a₆`, with the integral coefficients `-(5σ₃(N) + 7σ₅(N))/12`
(see `twelve_dvd_sigma`). -/
def a6Series : PowerSeries ℤ :=
  PowerSeries.mk fun N => -((5 * ((ArithmeticFunction.sigma 3 N : ℕ) : ℤ) +
    7 * ((ArithmeticFunction.sigma 5 N : ℕ) : ℤ)) / 12)

/-- `12 ∣ 5σ₃(N) + 7σ₅(N)`, since `12 ∣ 5d³ + 7d⁵` for every divisor `d`. -/
theorem twelve_dvd_sigma (N : ℕ) : (12 : ℤ) ∣ 5 * ((ArithmeticFunction.sigma 3 N : ℕ) : ℤ) +
    7 * ((ArithmeticFunction.sigma 5 N : ℕ) : ℤ) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => twelve_dvd_five_mul_pow_three_add_seven_mul_pow_five d

/-- `12 a₆ = -(5 s₃ + 7 s₅)` as integer power series. -/
theorem a6Series_mul_twelve :
    a6Series * 12 = -(5 * lambertSeries 3 + 7 * lambertSeries 5) := by
  refine PowerSeries.ext fun N => ?_
  rw [← map_ofNat (PowerSeries.C (R := ℤ)) 12, ← map_ofNat (PowerSeries.C (R := ℤ)) 5,
    ← map_ofNat (PowerSeries.C (R := ℤ)) 7, PowerSeries.coeff_mul_C, map_neg, map_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  simp only [a6Series, lambertSeries, PowerSeries.coeff_mk]
  rw [neg_mul, Int.ediv_mul_cancel (twelve_dvd_sigma N)]

/-- `tate:prop:discriminant`, first clause, for `a₄`: `a₄(q)` is the Hahn evaluation of an
integer power series. -/
theorem tateA4_eq_heval {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    tateA4 q = PowerSeries.heval q (PowerSeries.map (Int.castRingHom k) a4Series) := by
  simp only [a4Series, map_mul, map_neg, map_ofNat]
  rw [← tateSum_eq_heval 3 hq, tateA4]

/-- `tate:prop:discriminant`, first clause, for `a₆`: `a₆(q)` is the Hahn evaluation of an
integer power series. This uses `12 ≠ 0` in `k`, which holds in the source's characteristic
zero; in characteristic `2` or `3`, `tateA6` is Lean's junk value. -/
theorem tateA6_eq_heval (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    tateA6 q = PowerSeries.heval q (PowerSeries.map (Int.castRingHom k) a6Series) := by
  have h12' : (12 : k⟦Γ⟧) ≠ 0 := by
    rw [← map_ofNat (C : k →+* k⟦Γ⟧) 12]
    exact C_ne_zero h12
  have h := congrArg (fun f => PowerSeries.heval q (PowerSeries.map (Int.castRingHom k) f))
    a6Series_mul_twelve
  simp only [map_mul, map_neg, map_add, map_ofNat, ← tateSum_eq_heval 3 hq,
    ← tateSum_eq_heval 5 hq] at h
  rw [tateA6, div_eq_iff h12', h]

theorem map_discrFormula {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (a4 a6 : A) :
    φ (discrFormula a4 a6) = discrFormula (φ a4) (φ a6) := by
  simp only [discrFormula, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]

/-- `Δ(q)` is the Hahn evaluation of the integer power series
`discrFormula a4Series a6Series`. The identity `tate:eq:Delta`, `Δ(q) = q ∏ (1 - qⁿ)²⁴`,
therefore reduces, given the compatibility of `PowerSeries.heval q` with the infinite product
(for example via `Surreal.HahnSeries.InfiniteProducts`), to the classical formal identity
`discrFormula a4Series a6Series = X ∏ (1 - Xⁿ)²⁴` in `ℤ⟦X⟧`. Neither is proved here. -/
theorem tateCurve_Δ_eq_heval (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) :
    (tateCurve q).Δ = PowerSeries.heval q
      (PowerSeries.map (Int.castRingHom k) (discrFormula a4Series a6Series)) := by
  have e : PowerSeries.heval q
      (PowerSeries.map (Int.castRingHom k) (discrFormula a4Series a6Series)) =
      discrFormula (PowerSeries.heval q (PowerSeries.map (Int.castRingHom k) a4Series))
        (PowerSeries.heval q (PowerSeries.map (Int.castRingHom k) a6Series)) :=
    map_discrFormula ((PowerSeries.heval q).toRingHom.comp
      (PowerSeries.map (Int.castRingHom k))) _ _
  rw [e, ← tateA4_eq_heval hq, ← tateA6_eq_heval h12 hq, tateCurve_Δ, discrFormula]

/-! ### `q j(q)` as the Hahn evaluation of an integer power series -/

/-- The integer power series with `a4Series = X * a4Shift`. -/
def a4Shift : PowerSeries ℤ :=
  PowerSeries.mk fun n => -5 * ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℤ)

/-- The integer power series with `a6Series = X * a6Shift`. -/
def a6Shift : PowerSeries ℤ :=
  PowerSeries.mk fun n => -((5 * ((ArithmeticFunction.sigma 3 (n + 1) : ℕ) : ℤ) +
    7 * ((ArithmeticFunction.sigma 5 (n + 1) : ℕ) : ℤ)) / 12)

theorem a4Series_eq_X_mul : a4Series = PowerSeries.X * a4Shift := by
  refine PowerSeries.ext fun n => ?_
  rw [a4Series, ← map_ofNat (PowerSeries.C (R := ℤ)) 5, ← map_neg, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [lambertSeries]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp [lambertSeries, a4Shift]

theorem a6Series_eq_X_mul : a6Series = PowerSeries.X * a6Shift := by
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero => simp [a6Series]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp [a6Series, a6Shift]

/-- The integer power series `Δ/X` (`discrFormula_eq_X_mul`), a unit of `ℤ⟦X⟧` with constant
coefficient `1` (`isUnit_discrUnit`, `constantCoeff_discrUnit`). -/
def discrUnit : PowerSeries ℤ :=
  -a6Shift + PowerSeries.X * (a4Shift ^ 2 - 64 * PowerSeries.X * a4Shift ^ 3 -
    432 * a6Shift ^ 2 + 72 * a4Shift * a6Shift)

theorem discrFormula_eq_X_mul :
    discrFormula a4Series a6Series = PowerSeries.X * discrUnit := by
  rw [a4Series_eq_X_mul, a6Series_eq_X_mul, discrFormula, discrUnit]
  ring

theorem constantCoeff_discrUnit : PowerSeries.constantCoeff discrUnit = 1 := by
  simp [discrUnit, a6Shift, ArithmeticFunction.sigma_apply]

/-- `Δ/X` is a unit of `ℤ⟦X⟧`, as its constant coefficient is `1`. -/
theorem isUnit_discrUnit : IsUnit discrUnit :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_discrUnit]; exact isUnit_one)

/-- The integer power series `c₄³ (Δ/X)⁻¹`. -/
def jSeries : PowerSeries ℤ :=
  c4Formula a4Series ^ 3 * PowerSeries.invOfUnit discrUnit 1

theorem map_c4Formula {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (a4 : A) :
    φ (c4Formula a4) = c4Formula (φ a4) := by
  simp only [c4Formula, map_sub, map_one, map_mul, map_ofNat]

/-- `tate:eq:j`, Laurent-series clause: `q j(q)` is the Hahn evaluation of the integer power
series `jSeries`, so `j(q) = q⁻¹ jSeries(q)` is the evaluation of an integer Laurent series. -/
theorem mul_tateCurve_j_eq_heval (h12 : (12 : k) ≠ 0) {q : k⟦Γ⟧} {α : Γ}
    (hα : q.orderTop = α) (hα0 : 0 < α) [(tateCurve q).IsElliptic] :
    q * (tateCurve q).j = PowerSeries.heval q (PowerSeries.map (Int.castRingHom k) jSeries) := by
  have hq := orderTop_pos_of_eq hα hα0
  set φ : PowerSeries ℤ →+* k⟦Γ⟧ :=
    (PowerSeries.heval q).toRingHom.comp (PowerSeries.map (Int.castRingHom k))
  have hX : φ PowerSeries.X = q := by
    change PowerSeries.heval q (PowerSeries.map (Int.castRingHom k) PowerSeries.X) = q
    rw [PowerSeries.map_X, PowerSeries.heval_X q hq]
  have hΔ : (tateCurve q).Δ = q * φ discrUnit := by
    rw [tateCurve_Δ_eq_heval h12 hq]
    change φ (discrFormula a4Series a6Series) = _
    rw [discrFormula_eq_X_mul, map_mul, hX]
  have hinv : φ discrUnit * φ (PowerSeries.invOfUnit discrUnit 1) = 1 := by
    rw [← map_mul, PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_discrUnit, Units.val_one]),
      map_one]
  have hc4 : (tateCurve q).c₄ = φ (c4Formula a4Series) := by
    rw [map_c4Formula, tateCurve_c₄, tateA4_eq_heval hq, c4Formula]
    rfl
  have hΔ0 := tateCurve_Δ_ne_zero h12 hα hα0
  change q * (tateCurve q).j = φ jSeries
  rw [jSeries, map_mul, map_pow, ← hc4, tateCurve_j, mul_div_assoc', div_eq_iff hΔ0, hΔ]
  linear_combination (-(q * (tateCurve q).c₄ ^ 3)) * hinv

end

end Surreal.TateDiscriminant
