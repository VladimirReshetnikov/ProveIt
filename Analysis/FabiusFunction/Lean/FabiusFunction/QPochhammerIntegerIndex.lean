import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.QPochhammerElementaryIdentities
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals

/-!
# q-Pochhammer symbols with integer indices

The finite symbol `(a;q)_n = ∏_{0 ≤ j < n} (1 - a q^j)` extends to all integer
indices through *signed interval products*: for integers `u ≤ v` put

`I(u,v) = ∏_{u ≤ j < v} (1 - a q^j)`,  and  `I(v,u) = I(u,v)⁻¹`.

Then `(a;q)_n := I(0,n)` for every `n ∈ ℤ`, which for `n = -m < 0` is the
reciprocal `1/(aq^{-m};q)_m`, and the shifted symbol `(aq^m;q)_n` is `I(m,m+n)`.

The interval products satisfy the **cocycle identity**
`I(u,w) = I(u,v) I(v,w)` for all integers `u, v, w`, as soon as the two factors
are nonzero (for `u ≤ v ≤ w` it holds unconditionally).  This single identity
contains the concatenation law `(a;q)_{m+n} = (a;q)_m (aq^m;q)_n` for all
integer `m, n`, the shift `(a;q)_{n+1} = (a;q)_n (1 - aq^n)`, and the
closed form `(a;q)_{-n} = (-1)^n a^{-n} q^{\binom{n+1}{2}} / (q/a;q)_n`.

## Main declarations

* `qIntervalProd`: the signed interval product `I(u,v)`.
* `qIntervalProd_symm`, `qIntervalProd_trans_of_le`, `qIntervalProd_trans`:
  antisymmetry and the cocycle identity.
* `finiteQPochhammerZ`: the symbol with an integer index, with
  `finiteQPochhammerZ_natCast` and `finiteQPochhammerZ_neg_natCast`.
* `finiteQPochhammerZ_add`, `finiteQPochhammerZ_add_one`: concatenation and
  shift for integer indices.
* `finiteQPochhammerZ_neg_natCast_eq`: the closed form for a negative index.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-- An integer interval of natural length is the image of a range. -/
theorem Ico_int_eq_image_range (u : ℤ) (n : ℕ) :
    Finset.Ico u (u + n) = (Finset.range n).image (fun s : ℕ => u + (s : ℤ)) := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(x - u).toNat, by omega, by omega⟩
  · rintro ⟨s, hs, rfl⟩
    omega

/-- Products over an integer interval of natural length reindex to a range. -/
theorem prod_Ico_int_eq_prod_range {M : Type*} [CommMonoid M] (f : ℤ → M) (u : ℤ) (n : ℕ) :
    ∏ j ∈ Finset.Ico u (u + n), f j = ∏ s ∈ Finset.range n, f (u + s) := by
  rw [Ico_int_eq_image_range, Finset.prod_image]
  intro a _ b _ h
  exact_mod_cast add_left_cancel h

variable {K : Type*} [Field K]

/-- The signed interval product `I(u,v) = ∏_{u ≤ j < v} (1 - a q^j)` for `u ≤ v`,
and `I(u,v) = I(v,u)⁻¹` for `u > v`. -/
noncomputable def qIntervalProd (a q : K) (u v : ℤ) : K :=
  if u ≤ v then ∏ j ∈ Finset.Ico u v, (1 - a * q ^ j)
  else (∏ j ∈ Finset.Ico v u, (1 - a * q ^ j))⁻¹

/-- The `q`-Pochhammer symbol `(a;q)_n` with an integer index `n`, as `I(0,n)`. -/
noncomputable def finiteQPochhammerZ (a q : K) (n : ℤ) : K :=
  qIntervalProd a q 0 n

variable {a q : K}

/-- On a forward interval, `qIntervalProd` is the ordinary finite product. -/
theorem qIntervalProd_of_le {u v : ℤ} (h : u ≤ v) :
    qIntervalProd a q u v = ∏ j ∈ Finset.Ico u v, (1 - a * q ^ j) :=
  if_pos h

/-- On a reversed interval, `qIntervalProd` is the inverse of the corresponding
forward product. -/
theorem qIntervalProd_of_lt {u v : ℤ} (h : v < u) :
    qIntervalProd a q u v = (∏ j ∈ Finset.Ico v u, (1 - a * q ^ j))⁻¹ :=
  if_neg (not_le.mpr h)

/-- The signed product over an empty integer interval is one. -/
@[simp] theorem qIntervalProd_self (u : ℤ) : qIntervalProd a q u u = 1 := by
  simp [qIntervalProd]

/-- Reversing the interval inverts the product. -/
theorem qIntervalProd_symm (u v : ℤ) :
    qIntervalProd a q v u = (qIntervalProd a q u v)⁻¹ := by
  rcases lt_trichotomy u v with h | rfl | h
  · rw [qIntervalProd_of_lt h, qIntervalProd_of_le h.le]
  · simp
  · rw [qIntervalProd_of_le h.le, qIntervalProd_of_lt h, inv_inv]

/-- The cocycle identity for `u ≤ v ≤ w`, unconditionally. -/
theorem qIntervalProd_trans_of_le {u v w : ℤ} (huv : u ≤ v) (hvw : v ≤ w) :
    qIntervalProd a q u w = qIntervalProd a q u v * qIntervalProd a q v w := by
  rw [qIntervalProd_of_le (huv.trans hvw), qIntervalProd_of_le huv, qIntervalProd_of_le hvw,
    ← Finset.prod_union (Finset.Ico_disjoint_Ico_consecutive u v w),
    Finset.Ico_union_Ico_eq_Ico huv hvw]

/-- **The cocycle identity** `I(u,w) = I(u,v) I(v,w)` for all integers `u, v, w`,
whenever the two factors are nonzero. -/
theorem qIntervalProd_trans {u v w : ℤ} (huv : qIntervalProd a q u v ≠ 0)
    (hvw : qIntervalProd a q v w ≠ 0) :
    qIntervalProd a q u w = qIntervalProd a q u v * qIntervalProd a q v w := by
  rcases le_total u v with h1 | h1
  · rcases le_total v w with h2 | h2
    · exact qIntervalProd_trans_of_le h1 h2
    · rcases le_total u w with h3 | h3
      · -- u ≤ w ≤ v
        have e1 : qIntervalProd a q u v = qIntervalProd a q u w * qIntervalProd a q w v :=
          qIntervalProd_trans_of_le h3 h2
        have hne : qIntervalProd a q w v ≠ 0 :=
          right_ne_zero_of_mul (by rw [← e1]; exact huv)
        rw [e1, qIntervalProd_symm w v, mul_inv_cancel_right₀ hne]
      · -- w ≤ u ≤ v
        have e1 : qIntervalProd a q w v = qIntervalProd a q w u * qIntervalProd a q u v :=
          qIntervalProd_trans_of_le h3 h1
        rw [qIntervalProd_symm w u, qIntervalProd_symm w v, e1, mul_inv,
          mul_comm (qIntervalProd a q w u)⁻¹, mul_inv_cancel_left₀ huv]
  · rcases le_total v w with h2 | h2
    · rcases le_total u w with h3 | h3
      · -- v ≤ u ≤ w
        have e1 : qIntervalProd a q v w = qIntervalProd a q v u * qIntervalProd a q u w :=
          qIntervalProd_trans_of_le h1 h3
        have hne : qIntervalProd a q v u ≠ 0 := fun h =>
          huv (by rw [qIntervalProd_symm v u, h, inv_zero])
        rw [qIntervalProd_symm v u, e1, inv_mul_cancel_left₀ hne]
      · -- v ≤ w ≤ u
        have e1 : qIntervalProd a q v u = qIntervalProd a q v w * qIntervalProd a q w u :=
          qIntervalProd_trans_of_le h2 h3
        rw [qIntervalProd_symm w u, qIntervalProd_symm v u, e1, mul_inv,
          mul_comm ((qIntervalProd a q v w)⁻¹ * (qIntervalProd a q w u)⁻¹),
          mul_inv_cancel_left₀ hvw]
    · -- w ≤ v ≤ u
      have e1 : qIntervalProd a q w u = qIntervalProd a q w v * qIntervalProd a q v u :=
        qIntervalProd_trans_of_le h2 h1
      rw [qIntervalProd_symm w u, qIntervalProd_symm v u, qIntervalProd_symm w v, e1, mul_inv,
        mul_comm (qIntervalProd a q w v)⁻¹]

/-- For a natural index the integer-index symbol is the finite symbol. -/
theorem finiteQPochhammerZ_natCast (n : ℕ) :
    finiteQPochhammerZ a q n = finiteQPochhammerIn a q n := by
  have h := prod_Ico_int_eq_prod_range (fun j : ℤ => 1 - a * q ^ j) 0 n
  simp only [zero_add, zpow_natCast] at h
  rw [finiteQPochhammerZ, qIntervalProd_of_le (by omega : (0 : ℤ) ≤ n), h, finiteQPochhammerIn]

/-- For a negative index `-n` the symbol is the reciprocal of the product of the
`n` factors with exponents `-n, …, -1`. -/
theorem finiteQPochhammerZ_neg_natCast (n : ℕ) :
    finiteQPochhammerZ a q (-n) =
      (∏ s ∈ Finset.range n, (1 - a * q ^ (-(n : ℤ) + s)))⁻¹ := by
  have h := prod_Ico_int_eq_prod_range (fun j : ℤ => 1 - a * q ^ j) (-n) n
  rw [show (-(n : ℤ) + n) = 0 by omega] at h
  rw [finiteQPochhammerZ, qIntervalProd_symm, qIntervalProd_of_le (by omega : -(n : ℤ) ≤ 0), h]

/-- Shifting an interval by `m` shifts the parameter by `q^m`. -/
theorem prod_Ico_add_zpow (hq : q ≠ 0) (m u v : ℤ) :
    ∏ j ∈ Finset.Ico (u + m) (v + m), (1 - a * q ^ j) =
      ∏ j ∈ Finset.Ico u v, (1 - a * q ^ m * q ^ j) := by
  rw [← Finset.prod_Ico_add']
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_add₀ hq, mul_comm (q ^ j), ← mul_assoc]

/-- The shifted symbol `(aq^m;q)_n` is the interval product `I(m, m+n)`. -/
theorem qIntervalProd_add_eq (hq : q ≠ 0) (m n : ℤ) :
    qIntervalProd a q m (m + n) = finiteQPochhammerZ (a * q ^ m) q n := by
  rcases le_or_gt 0 n with hn | hn
  · rw [qIntervalProd_of_le (by omega : m ≤ m + n), finiteQPochhammerZ, qIntervalProd_of_le hn,
      ← prod_Ico_add_zpow hq m, zero_add, add_comm n m]
  · rw [qIntervalProd_of_lt (by omega : m + n < m), finiteQPochhammerZ, qIntervalProd_of_lt hn,
      ← prod_Ico_add_zpow hq m, zero_add, add_comm n m]

/-- **Concatenation with integer indices**: `(a;q)_{m+n} = (a;q)_m (aq^m;q)_n` for
all integers `m, n`, whenever both factors are nonzero. -/
theorem finiteQPochhammerZ_add (hq : q ≠ 0) {m n : ℤ} (hm : finiteQPochhammerZ a q m ≠ 0)
    (hn : finiteQPochhammerZ (a * q ^ m) q n ≠ 0) :
    finiteQPochhammerZ a q (m + n) =
      finiteQPochhammerZ a q m * finiteQPochhammerZ (a * q ^ m) q n := by
  rw [← qIntervalProd_add_eq hq] at hn ⊢
  exact qIntervalProd_trans hm hn

/-- **The shift** `(a;q)_{n+1} = (a;q)_n (1 - aq^n)` for every integer `n`, whenever
both factors are nonzero. -/
theorem finiteQPochhammerZ_add_one {n : ℤ} (hn : finiteQPochhammerZ a q n ≠ 0)
    (h : 1 - a * q ^ n ≠ 0) :
    finiteQPochhammerZ a q (n + 1) = finiteQPochhammerZ a q n * (1 - a * q ^ n) := by
  have h1 : qIntervalProd a q n (n + 1) = 1 - a * q ^ n := by
    have hs : Finset.Ico n (n + 1) = {n} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [qIntervalProd_of_le (by omega : n ≤ n + 1), hs, Finset.prod_singleton]
  have hvw : qIntervalProd a q n (n + 1) ≠ 0 := by rw [h1]; exact h
  show qIntervalProd a q 0 (n + 1) = qIntervalProd a q 0 n * (1 - a * q ^ n)
  rw [qIntervalProd_trans hn hvw, h1]

/-- **Closed form for a negative index**:
`(a;q)_{-n} = (-1)^n a^{-n} q^{\binom{n+1}{2}} / (q/a;q)_n` for `a ≠ 0`, `q ≠ 0`. -/
theorem finiteQPochhammerZ_neg_natCast_eq (ha : a ≠ 0) (hq : q ≠ 0) (n : ℕ) :
    finiteQPochhammerZ a q (-n) =
      (-1) ^ n * a⁻¹ ^ n * q ^ (n + 1).choose 2 / finiteQPochhammerIn (q / a) q n := by
  have key : ∏ s ∈ Finset.range n, (1 - a * q ^ (-(n : ℤ) + s)) =
      (-a) ^ n * q⁻¹ ^ (n + 1).choose 2 * finiteQPochhammerIn (q / a) q n := by
    have h1 : ∏ s ∈ Finset.range n, (1 - a * q ^ (-(n : ℤ) + s)) =
        ∏ s ∈ Finset.range n, (1 - a * q⁻¹ ^ (n - s)) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hs' : s < n := Finset.mem_range.mp hs
      rw [show (-(n : ℤ) + s) = -((n - s : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← inv_pow]
    have h2 : ∏ s ∈ Finset.range n, (1 - a * q⁻¹ ^ (n - s)) =
        finiteQPochhammerIn (a * q⁻¹) q⁻¹ n := by
      rw [finiteQPochhammerIn, ← Finset.prod_range_reflect]
      refine Finset.prod_congr rfl fun s hs => ?_
      have hs' : s < n := Finset.mem_range.mp hs
      rw [show n - (n - 1 - s) = s + 1 by omega, pow_succ', ← mul_assoc]
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [h1, h2, finiteQPochhammerIn_inv_base_reversal _ _ (mul_ne_zero ha (inv_ne_zero hq)) hq,
      mul_inv, inv_inv, div_eq_mul_inv, mul_comm q a⁻¹, hc, pow_add, neg_pow, neg_pow a, mul_pow]
    ring
  rw [finiteQPochhammerZ_neg_natCast, key, mul_inv, mul_inv, ← inv_pow, ← inv_pow, inv_inv,
    inv_neg, neg_pow]
  exact (div_eq_mul_inv _ _).symm

end Fabius
