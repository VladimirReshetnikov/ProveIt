import FabiusFunction.PrimitiveRootBlock
import FabiusFunction.QPochhammerDissection

/-!
# The q-Lucas theorem

Let `ζ` be a primitive `d`-th root of unity in an integral domain, and write
`n = ad + b`, `m = rd + s` with `0 ≤ b, s < d`.  Then

`[ad + b, rd + s]_ζ = \binom ar · [b, s]_ζ`.

The proof compares coefficients of `x^{rd+s}` in the finite `q`-binomial
theorem at `q = ζ`,

`∏_{j<ad+b} (1 + x ζ^j) = ∑_h ζ^{\binom h2} [ad+b, h]_ζ x^h`.

Grouping the product into `a` complete root-of-unity blocks, each equal to
`1 - (-x)^d`, and one incomplete block `∏_{j<b} (1 + xζ^j)` of degree `< d`,
the coefficient of `x^{rd+s}` on the product side is
`\binom ar (-1)^{r(d+1)} ζ^{\binom s2} [b,s]_ζ`, and the phase
`ζ^{\binom{rd+s}2}` equals `(-1)^{r(d+1)} ζ^{\binom s2}`.

## Main declarations

* `coeff_finiteQPochhammerIn_neg_X`: coefficients of `∏_{j<n}(1 + Xζ^j)`.
* `finiteQPochhammerIn_neg_X_block`: the block factorization.
* `coeff_block_pow_mul`: the coefficient of `X^{rd+s}` in `(1 - (-X)^d)^a B`.
* `pow_choose_two_add_mul_eq`: the phase identity.
* `gaussianBinomial_q_lucas`: the `q`-Lucas theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

/-- `2 · \binom n2 = n(n-1)`. -/
theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

/-- The quadratic identity behind Vandermonde for `\binom{·}{2}`, in `ℕ`. -/
theorem add_mul_add_sub_one (x s : ℕ) :
    (x + s) * (x + s - 1) = x * (x - 1) + 2 * (x * s) + s * (s - 1) := by
  rw [Nat.mul_sub_one, Nat.mul_sub_one, Nat.mul_sub_one]
  have h1 := Nat.le_mul_self x
  have h2 := Nat.le_mul_self s
  have h3 := Nat.le_mul_self (x + s)
  zify [h1, h2, h3]
  ring

/-- Vandermonde for `\binom{·}{2}`: `\binom{x+s}{2} = \binom x2 + xs + \binom s2`. -/
theorem choose_two_add (x s : ℕ) : (x + s).choose 2 = x.choose 2 + x * s + s.choose 2 := by
  have e1 := two_mul_choose_two (x + s)
  have e2 := two_mul_choose_two x
  have e3 := two_mul_choose_two s
  have := add_mul_add_sub_one x s
  omega

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- The coefficients of `∏_{j<n} (1 + X ζ^j)`: `ζ^{\binom m2} [n,m]_ζ` for every `m`. -/
theorem coeff_finiteQPochhammerIn_neg_X (ζ : R) (n m : ℕ) :
    (finiteQPochhammerIn (-X : R[X]) (C ζ) n).coeff m =
      ζ ^ m.choose 2 * gaussianBinomial ζ n m := by
  rw [← finite_qBinomial_theorem (C ζ) (-X) n]
  have h : ∀ k, (-1 : R[X]) ^ k * (C ζ) ^ k.choose 2 * gaussianBinomial (C ζ) n k * (-X) ^ k =
      C (ζ ^ k.choose 2 * gaussianBinomial ζ n k) * X ^ k := by
    intro k
    rw [← map_gaussianBinomial C, ← C_pow, C_mul]
    have hk : (-1 : R[X]) ^ k * (-X) ^ k = X ^ k := by rw [← mul_pow, neg_mul_neg, one_mul]
    linear_combination (C (ζ ^ k.choose 2) * C (gaussianBinomial ζ n k)) * hk
  simp_rw [h]
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · rw [Finset.mem_range] at hm
    rw [gaussianBinomial_eq_zero_of_lt _ (by omega), mul_zero]

/-- **Block factorization**: `∏_{j<ad+b} (1 + Xζ^j) = (1 - (-X)^d)^a ∏_{j<b} (1 + Xζ^j)` for a
primitive `d`-th root of unity `ζ`. -/
theorem finiteQPochhammerIn_neg_X_block {ζ : R} {d : ℕ} (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (a b : ℕ) :
    finiteQPochhammerIn (-X : R[X]) (C ζ) (a * d + b) =
      (1 - (-X) ^ d) ^ a * finiteQPochhammerIn (-X : R[X]) (C ζ) b := by
  have hζC : IsPrimitiveRoot (C ζ : R[X]) d := hζ.map_of_injective C_injective
  have hCd : (C ζ : R[X]) ^ d = 1 := by rw [← C_pow, hζ.pow_eq_one, C_1]
  rw [finiteQPochhammerIn_add, mul_comm a d, finiteQPochhammerIn_dissection, pow_mul, hCd,
    one_pow, mul_one]
  congr 1
  rw [← finiteQPochhammerIn_isPrimitiveRoot hd hζC (-X)]
  unfold finiteQPochhammerIn
  rw [← Finset.prod_pow]
  refine prod_congr rfl fun s _ => ?_
  simp [Finset.prod_const]

omit [IsDomain R] in
/-- The coefficient of `X^{rd+s}` (`s < d`) in `(1 - (-X)^d)^a · B` for `B` of degree `< d`:
only the `r`-th binomial term contributes. -/
theorem coeff_block_pow_mul {d : ℕ} (a r s : ℕ) (hs : s < d) (B : R[X])
    (hB : B.natDegree < d) :
    ((1 - (-X : R[X]) ^ d) ^ a * B).coeff (r * d + s) =
      (a.choose r : R) * ((-1 : R) ^ (d + 1)) ^ r * B.coeff s := by
  have hu : (1 - (-X : R[X]) ^ d) = C ((-1 : R) ^ (d + 1)) * X ^ d + 1 := by
    rw [neg_pow, pow_succ, C_mul, C_pow, C_neg, C_1]
    ring
  rw [hu, add_pow, Finset.sum_mul, finsetSum_coeff]
  have hterm : ∀ i ∈ range (a + 1),
      ((C ((-1 : R) ^ (d + 1)) * X ^ d) ^ i * 1 ^ (a - i) * ((a.choose i : ℕ) : R[X]) * B).coeff
        (r * d + s) =
      (a.choose i : R) * ((-1 : R) ^ (d + 1)) ^ i *
        (if i * d ≤ r * d + s then B.coeff (r * d + s - i * d) else 0) := by
    intro i _
    rw [one_pow, mul_one, mul_pow, ← C_pow, ← pow_mul X d i, ← C_eq_natCast,
      show C (((-1 : R) ^ (d + 1)) ^ i) * X ^ (d * i) * C ((a.choose i : ℕ) : R) * B =
        C ((a.choose i : R) * ((-1 : R) ^ (d + 1)) ^ i) * (X ^ (i * d) * B) by
        rw [C_mul, mul_comm d i]; ring,
      coeff_C_mul, coeff_X_pow_mul']
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single r]
  · rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  · intro i _ hir
    rcases Nat.lt_or_gt_of_ne hir with hlt | hgt
    · have h1 : i * d + d ≤ r * d := by nlinarith
      rw [if_pos (by omega), coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
    · have h2 : r * d + d ≤ i * d := by nlinarith
      rw [if_neg (by omega), mul_zero]
  · intro hr
    rw [Finset.mem_range, not_lt] at hr
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]

/-- **The phase**: `ζ^{\binom{rd+s}2} = ((-1)^{d+1})^r ζ^{\binom s2}` for a primitive `d`-th
root of unity `ζ`. -/
theorem pow_choose_two_add_mul_eq {ζ : R} {d : ℕ} (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (r s : ℕ) :
    ζ ^ (r * d + s).choose 2 = ((-1 : R) ^ (d + 1)) ^ r * ζ ^ s.choose 2 := by
  rw [choose_two_add, pow_add, pow_add, show r * d * s = r * s * d by ring, pow_mul',
    hζ.pow_eq_one, one_pow, mul_one]
  congr 1
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- d = m + m: ζ^m = -1
    have hm0 : 0 < m := by omega
    have hζm : ζ ^ m = -1 :=
      (hζ.pow hd (by omega : d = m * 2)).eq_neg_one_of_two_right
    have hc : (r * d).choose 2 = (r * m) * (r * (m + m) - 1) := by
      rw [Nat.choose_two_right, hm,
        show r * (m + m) * (r * (m + m) - 1) = 2 * ((r * m) * (r * (m + m) - 1)) by ring,
        Nat.mul_div_cancel_left _ two_pos]
    have hodd : Odd (m + m + 1) := ⟨m, by ring⟩
    rw [hc, pow_mul, pow_mul', hζm, hm, Odd.neg_one_pow hodd]
    rcases Nat.even_or_odd r with hr | hr
    · rw [hr.neg_one_pow, one_pow]
    · rw [hr.neg_one_pow]
      have h2 : r * (m + m) = 2 * (r * m) := by ring
      have hrm : 1 ≤ r * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hr.pos.ne' hm0.ne')
      exact Odd.neg_one_pow ⟨r * m - 1, by omega⟩
  · -- d = 2m + 1: C(rd,2) is a multiple of d
    have hev : Even (r * (r * d - 1)) := by
      rcases Nat.even_or_odd r with hr | hr
      · exact hr.mul_right _
      · have h1 : Odd (r * d) := hr.mul ⟨m, hm⟩
        exact (Nat.Odd.sub_odd h1 odd_one).mul_left r
    obtain ⟨t, ht⟩ := hev
    have hc : (r * d).choose 2 = d * t := by
      rw [Nat.choose_two_right, show r * d * (r * d - 1) = d * (r * (r * d - 1)) by ring, ht,
        show d * (t + t) = 2 * (d * t) by ring, Nat.mul_div_cancel_left _ two_pos]
    rw [hc, pow_mul, hζ.pow_eq_one, one_pow, hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
      pow_mul, neg_one_sq, one_pow, one_pow]

/-- **The `q`-Lucas theorem**: for a primitive `d`-th root of unity `ζ` in an integral
domain and `0 ≤ b, s < d`,
`[ad + b, rd + s]_ζ = \binom ar · [b,s]_ζ`. -/
theorem gaussianBinomial_q_lucas {ζ : R} {d : ℕ} (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (a r : ℕ) {b s : ℕ} (hb : b < d) (hs : s < d) :
    gaussianBinomial ζ (a * d + b) (r * d + s) = (a.choose r : R) * gaussianBinomial ζ b s := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hd.ne'
  -- degree of the incomplete block
  have hB : (finiteQPochhammerIn (-X : R[X]) (C ζ) b).natDegree < d := by
    refine lt_of_le_of_lt ?_ hb
    unfold finiteQPochhammerIn
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ j ∈ range b, (1 - -X * C ζ ^ j : R[X]).natDegree ≤ ∑ j ∈ range b, 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [neg_mul, sub_neg_eq_add]
          exact (natDegree_add_le _ _).trans (max_le (natDegree_one.le.trans zero_le_one)
            (natDegree_mul_le.trans
              (by rw [← C_pow, natDegree_C, add_zero]; exact natDegree_X_le)))
      _ = b := by simp
  -- the two coefficient computations
  have h1 := coeff_finiteQPochhammerIn_neg_X ζ (a * d + b) (r * d + s)
  have h2 := coeff_block_pow_mul a r s hs _ hB
  rw [finiteQPochhammerIn_neg_X_block hd hζ, h2, coeff_finiteQPochhammerIn_neg_X,
    pow_choose_two_add_mul_eq hd hζ] at h1
  -- cancel the nonzero phase
  have hne : ((-1 : R) ^ (d + 1)) ^ r * ζ ^ s.choose 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))) (pow_ne_zero _ hζ0)
  refine mul_left_cancel₀ hne ?_
  rw [← h1]
  ring

end Fabius
