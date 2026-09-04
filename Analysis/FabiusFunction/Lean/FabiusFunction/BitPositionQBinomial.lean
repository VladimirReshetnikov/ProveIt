import FabiusFunction.BitPositionGenerating
import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.ThueMorseEnumerators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Order.Interval.Finset.Basic

/-!
# The q-binomial grading of a dyadic block

The bit-position generating identity

`∏_{j<N} (1 + y·qʲ) = ∑_{n<2ᴺ} y^{w(n)}·q^{σ(n)}`

grades a dyadic block by two statistics at once: the binary weight
`w(n)` and the bit-position sum `σ(n)`.  This module reads off the
`y^r`-graded piece.  On the product side the same expansion is Gauss's
binomial formula, so every graded piece is a Gaussian polynomial:

`∑_{n<2ᴺ, w(n)=r} q^{σ(n)} = q^{C(r,2)} · [N choose r]_q`.

The route is the corpus's own generating-function method, executed
literally: both expansions are read in `Polynomial R` at `y := X` and
`q := C q`, and the coefficients of `X^r` are compared.  No hypothesis
relating `r` and `N` is needed — above the diagonal the left side is an
empty sum and the Gaussian coefficient vanishes — and no hypothesis on
`q` is used, so everything holds at roots of unity, in positive
characteristic, and in the presence of zero divisors.

## Main declarations

* `prod_one_add_mul_pow_eq_gaussianBinomial` — **Gauss's binomial
  formula**, denominator-free, over every commutative ring: the finite
  `q`-binomial theorem at `z = -y`, where the two sign factors cancel.
* `prod_one_add_pow_eq_sum_gaussianBinomial` — its `y = 1` face.
* `sum_powersetCard_two_pow` — the **graded reindexing kernel**:
  size-`r` subsets of `range N` versus block elements of weight `r`.
* `sum_pow_bitPositionSum_filter_eq_gaussianBinomial` — **the graded
  identity**, and `..._eq_gaussianBinomial'` its triangular-exponent
  restatement `q^{r(r-1)/2}`.
* `sum_pow_sum_powersetCard_eq_gaussianBinomial` — the subset-side
  face: the Gaussian polynomial enumerates size-`r` subsets of
  `range N` by their sum.
* `sum_pow_sum_powersetCard_Icc_eq_gaussianBinomial` — the equivalent
  one-based subset formula on the interval `1, ..., N`.
* `gaussianBinomial_one_eq_choose` — the `q = 1` shadow, matching the
  atlas count `card_filter_binaryWeight_eq`; and
  `gaussianBinomial_one_eq_choose_ring`, the same shadow in every ring.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Gauss's binomial formula -/

/-- **Gauss's binomial formula**, denominator-free.  Over every
commutative ring,

`∏_{j<N} (1 + y·qʲ) = ∑_{k≤N} q^{C(k,2)}·[N choose k]_q·y^k`.

This is `finite_qBinomial_theorem` at `z = -y`: the sign `(-1)^k`
carried by the Gaussian summand is cancelled by the sign of `(-y)^k`,
leaving the positive expansion.  No division, cancellation, or
nonvanishing assumption on `q` is involved. -/
theorem prod_one_add_mul_pow_eq_gaussianBinomial {R : Type*}
    [CommRing R] (y q : R) (N : ℕ) :
    ∏ j ∈ range N, (1 + y * q ^ j) =
      ∑ k ∈ range (N + 1),
        q ^ k.choose 2 * gaussianBinomial q N k * y ^ k := by
  have hpoch :
      finiteQPochhammerIn (-y) q N =
        ∏ j ∈ range N, (1 + y * q ^ j) := by
    rw [finiteQPochhammerIn]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [← hpoch, ← finite_qBinomial_theorem q (-y) N]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hy : ((-1 : R) * (-y)) ^ k = y ^ k := by
    rw [neg_mul_neg, one_mul]
  calc
    (-1 : R) ^ k * q ^ k.choose 2 * gaussianBinomial q N k * (-y) ^ k
        = ((-1 : R) * (-y)) ^ k *
            (q ^ k.choose 2 * gaussianBinomial q N k) := by
      rw [mul_pow]; ring
    _ = q ^ k.choose 2 * gaussianBinomial q N k * y ^ k := by
      rw [hy]; ring

/-- The `y = 1` face of Gauss's formula: the total mass of a Gaussian
row weighted by the triangular powers of `q`. -/
theorem prod_one_add_pow_eq_sum_gaussianBinomial {R : Type*}
    [CommRing R] (q : R) (N : ℕ) :
    ∏ j ∈ range N, (1 + q ^ j) =
      ∑ k ∈ range (N + 1), q ^ k.choose 2 * gaussianBinomial q N k := by
  have h := prod_one_add_mul_pow_eq_gaussianBinomial (1 : R) q N
  simpa using h

/-! ## The graded reindexing kernel -/

/-- **Graded reindexing kernel.**  Encoding a finite set by distinct
two-powers matches the size-`r` subsets of `range N` with the elements
of the dyadic block `range (2 ^ N)` of binary weight `r`.  This is the
weight-graded refinement of `sum_powerset_two_pow`. -/
theorem sum_powersetCard_two_pow {M : Type*} [AddCommMonoid M]
    (N r : ℕ) (f : ℕ → M) :
    ∑ T ∈ powersetCard r (range N), f (∑ j ∈ T, 2 ^ j) =
      ∑ n ∈ {n ∈ range (2 ^ N) | binaryWeight n = r}, f n := by
  classical
  apply Finset.sum_bij (fun T _ => ∑ j ∈ T, 2 ^ j)
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨sum_two_pow_lt_two_pow hT.1,
      (binaryWeight_sum_two_pow_eq_card T).trans hT.2⟩
  · intro T _ S _ h
    exact sum_two_pow_injective h
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨bitSupport n, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨(bitSupport_subset_range_iff_lt_two_pow n N).mpr hn.1,
        (card_bitSupport n).trans hn.2⟩
    · exact sum_two_pow_bitSupport n
  · intro T _
    rfl

/-! ## Coefficient extraction in `Polynomial R` -/

/-- The `X^r` coefficient of the dyadic block read as a polynomial in
`X` with coefficients `q^{σ(n)}`. -/
private theorem coeff_sum_C_mul_X_pow_block {R : Type*} [CommRing R]
    (q : R) (N r : ℕ) :
    (∑ n ∈ range (2 ^ N),
        Polynomial.C (q ^ bitPositionSum n) *
          (Polynomial.X : Polynomial R) ^ binaryWeight n).coeff r =
      ∑ n ∈ {n ∈ range (2 ^ N) | binaryWeight n = r},
        q ^ bitPositionSum n := by
  calc
    (∑ n ∈ range (2 ^ N),
        Polynomial.C (q ^ bitPositionSum n) *
          (Polynomial.X : Polynomial R) ^ binaryWeight n).coeff r
        = ∑ n ∈ range (2 ^ N),
            (Polynomial.C (q ^ bitPositionSum n) *
              (Polynomial.X : Polynomial R) ^
                binaryWeight n).coeff r :=
      Polynomial.finsetSum_coeff _ _ _
    _ = ∑ n ∈ range (2 ^ N),
          if binaryWeight n = r then q ^ bitPositionSum n else 0 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases h : binaryWeight n = r
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]
    _ = ∑ n ∈ {n ∈ range (2 ^ N) | binaryWeight n = r},
          q ^ bitPositionSum n :=
      (Finset.sum_filter _ _).symm

/-- The `X^r` coefficient of the Gaussian row read as a polynomial in
`X`, before the diagonal case split. -/
private theorem coeff_sum_C_mul_X_pow_gauss {R : Type*} [CommRing R]
    (q : R) (N r : ℕ) :
    (∑ k ∈ range (N + 1),
        Polynomial.C (q ^ k.choose 2 * gaussianBinomial q N k) *
          (Polynomial.X : Polynomial R) ^ k).coeff r =
      ∑ k ∈ range (N + 1),
        if r = k then q ^ k.choose 2 * gaussianBinomial q N k
          else 0 := by
  calc
    (∑ k ∈ range (N + 1),
        Polynomial.C (q ^ k.choose 2 * gaussianBinomial q N k) *
          (Polynomial.X : Polynomial R) ^ k).coeff r
        = ∑ k ∈ range (N + 1),
            (Polynomial.C (q ^ k.choose 2 * gaussianBinomial q N k) *
              (Polynomial.X : Polynomial R) ^ k).coeff r :=
      Polynomial.finsetSum_coeff _ _ _
    _ = ∑ k ∈ range (N + 1),
          if r = k then q ^ k.choose 2 * gaussianBinomial q N k
            else 0 :=
      Finset.sum_congr rfl fun k _ =>
        Polynomial.coeff_C_mul_X_pow _ _ _

/-! ## The graded identity -/

/-- **The q-binomial grading of a dyadic block.**  For every
commutative ring, every level `N`, and every weight `r`,

`∑_{n < 2ᴺ, w(n) = r} q^{σ(n)} = q^{C(r,2)} · [N choose r]_q`,

where `w` is the binary weight and `σ` the bit-position sum.  The
identity is unconditional in `r`: for `r > N` the left side is an empty
sum and the Gaussian coefficient vanishes.

At `q = 1` it degenerates to the atlas count
`card_filter_binaryWeight_eq`; summing over `r` recovers the
bit-position enumerator `prod_one_add_pow_eq_sum_bitPositionSum`. -/
theorem sum_pow_bitPositionSum_filter_eq_gaussianBinomial
    {R : Type*} [CommRing R] (q : R) (N r : ℕ) :
    ∑ n ∈ {n ∈ range (2 ^ N) | binaryWeight n = r},
        q ^ bitPositionSum n =
      q ^ r.choose 2 * gaussianBinomial q N r := by
  have hmain :
      (∑ n ∈ range (2 ^ N),
          Polynomial.C (q ^ bitPositionSum n) *
            (Polynomial.X : Polynomial R) ^ binaryWeight n) =
        ∑ k ∈ range (N + 1),
          Polynomial.C (q ^ k.choose 2 * gaussianBinomial q N k) *
            (Polynomial.X : Polynomial R) ^ k := by
    calc
      (∑ n ∈ range (2 ^ N),
          Polynomial.C (q ^ bitPositionSum n) *
            (Polynomial.X : Polynomial R) ^ binaryWeight n)
          = ∑ n ∈ range (2 ^ N),
              (Polynomial.X : Polynomial R) ^ binaryWeight n *
                Polynomial.C q ^ bitPositionSum n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Polynomial.C_pow]
        exact mul_comm _ _
      _ = ∏ j ∈ range N,
            (1 + (Polynomial.X : Polynomial R) *
              Polynomial.C q ^ j) :=
        (prod_one_add_mul_pow_bitPositionSum
          (Polynomial.X : Polynomial R) (Polynomial.C q) N).symm
      _ = ∑ k ∈ range (N + 1),
            Polynomial.C q ^ k.choose 2 *
              gaussianBinomial (Polynomial.C q) N k *
                (Polynomial.X : Polynomial R) ^ k :=
        prod_one_add_mul_pow_eq_gaussianBinomial
          (Polynomial.X : Polynomial R) (Polynomial.C q) N
      _ = ∑ k ∈ range (N + 1),
            Polynomial.C (q ^ k.choose 2 * gaussianBinomial q N k) *
              (Polynomial.X : Polynomial R) ^ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Polynomial.C_mul, Polynomial.C_pow,
          map_gaussianBinomial
            (Polynomial.C : R →+* Polynomial R) q N k]
  have hcoeff :
      (∑ n ∈ range (2 ^ N),
          Polynomial.C (q ^ bitPositionSum n) *
            (Polynomial.X : Polynomial R) ^ binaryWeight n).coeff r =
        (∑ k ∈ range (N + 1),
          Polynomial.C (q ^ k.choose 2 * gaussianBinomial q N k) *
            (Polynomial.X : Polynomial R) ^ k).coeff r :=
    congrArg (fun p : Polynomial R => p.coeff r) hmain
  rw [coeff_sum_C_mul_X_pow_block q N r,
    coeff_sum_C_mul_X_pow_gauss q N r] at hcoeff
  by_cases hr : r ≤ N
  · have hmem : r ∈ range (N + 1) := Finset.mem_range.mpr (by omega)
    rw [hcoeff, Finset.sum_ite_eq_of_mem _ _ _ hmem]
  · have hlt : N < r := by omega
    rw [hcoeff, gaussianBinomial_eq_zero_of_lt q hlt, mul_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k < N + 1 := Finset.mem_range.mp hk
    exact if_neg (by omega)

/-- The graded identity with the triangular exponent written out:
`∑_{n < 2ᴺ, w(n) = r} q^{σ(n)} = q^{r(r-1)/2} · [N choose r]_q`. -/
theorem sum_pow_bitPositionSum_filter_eq_gaussianBinomial'
    {R : Type*} [CommRing R] (q : R) (N r : ℕ) :
    ∑ n ∈ {n ∈ range (2 ^ N) | binaryWeight n = r},
        q ^ bitPositionSum n =
      q ^ (r * (r - 1) / 2) * gaussianBinomial q N r := by
  rw [← Nat.choose_two_right]
  exact sum_pow_bitPositionSum_filter_eq_gaussianBinomial q N r

/-- **Subset-side face.**  The Gaussian polynomial `[N choose r]_q`,
shifted by the triangular power `q^{C(r,2)}`, is the generating
polynomial of the size-`r` subsets of `range N` by their sum:

`∑_{T ⊆ range N, |T| = r} q^{∑ T} = q^{C(r,2)} · [N choose r]_q`. -/
theorem sum_pow_sum_powersetCard_eq_gaussianBinomial
    {R : Type*} [CommRing R] (q : R) (N r : ℕ) :
    ∑ T ∈ powersetCard r (range N), q ^ (∑ j ∈ T, j) =
      q ^ r.choose 2 * gaussianBinomial q N r := by
  calc
    ∑ T ∈ powersetCard r (range N), q ^ (∑ j ∈ T, j)
        = ∑ T ∈ powersetCard r (range N),
            q ^ bitPositionSum (∑ j ∈ T, 2 ^ j) := by
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [bitPositionSum_sum_two_pow]
    _ = ∑ n ∈ {n ∈ range (2 ^ N) | binaryWeight n = r},
          q ^ bitPositionSum n :=
      sum_powersetCard_two_pow N r (fun n => q ^ bitPositionSum n)
    _ = q ^ r.choose 2 * gaussianBinomial q N r :=
      sum_pow_bitPositionSum_filter_eq_gaussianBinomial q N r

/-- **One-based subset-side face.**  Translating every element of a
size-`r` subset of `range N` upward by one adds `r` to its element sum.
Consequently

`sum_{T ⊆ {1, ..., N}, |T| = r} q^(sum T)
    = q^((r+1 choose 2)) * [N choose r]_q`.

This is the literal one-based form paired with
`sum_pow_sum_powersetCard_eq_gaussianBinomial`; it is total in `N` and
`r` and uses no hypothesis on `q`. -/
theorem sum_pow_sum_powersetCard_Icc_eq_gaussianBinomial
    {R : Type*} [CommRing R] (q : R) (N r : ℕ) :
    ∑ T ∈ powersetCard r (Icc 1 N), q ^ (∑ j ∈ T, j) =
      q ^ (r + 1).choose 2 * gaussianBinomial q N r := by
  let e : ℕ ↪ ℕ :=
    ⟨fun j => 1 + j, fun _ _ h => Nat.add_left_cancel h⟩
  have hIcc : (range N).map e = Icc 1 N := by
    ext j
    simp only [mem_map, mem_range, mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      change 1 ≤ 1 + i ∧ 1 + i ≤ N
      omega
    · intro hj
      refine ⟨j - 1, by omega, ?_⟩
      change 1 + (j - 1) = j
      omega
  rw [← hIcc, powersetCard_map, Finset.sum_map]
  calc
    ∑ T ∈ powersetCard r (range N), q ^ (∑ j ∈ T.map e, j) =
        ∑ T ∈ powersetCard r (range N), q ^ ((∑ j ∈ T, j) + r) := by
      apply Finset.sum_congr rfl
      intro T hT
      congr 1
      rw [Finset.sum_map]
      have hcard : T.card = r := (Finset.mem_powersetCard.mp hT).2
      change T.sum (fun x => 1 + x) = T.sum id + r
      rw [Finset.sum_add_distrib]
      simp [hcard]
      omega
    _ = q ^ r * ∑ T ∈ powersetCard r (range N), q ^ (∑ j ∈ T, j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _hT
      rw [pow_add]
      ring
    _ = q ^ r * (q ^ r.choose 2 * gaussianBinomial q N r) := by
      rw [sum_pow_sum_powersetCard_eq_gaussianBinomial]
    _ = q ^ (r + 1).choose 2 * gaussianBinomial q N r := by
      have hchoose : (r + 1).choose 2 = r.choose 2 + r := by
        simpa [Nat.add_comm] using Nat.choose_succ_succ r 1
      rw [hchoose, pow_add]
      ring

/-! ## The `q = 1` shadow -/

/-- **The `q = 1` shadow.**  The recursive Gaussian coefficient
specializes at `q = 1` to the ordinary binomial coefficient.  This is
the graded identity read at `q = 1`, where the left side counts the
integers of binary weight `r` in a dyadic block of level `N`. -/
theorem gaussianBinomial_one_eq_choose (N r : ℕ) :
    gaussianBinomial (1 : ℤ) N r = (N.choose r : ℤ) := by
  have h := sum_pow_bitPositionSum_filter_eq_gaussianBinomial
    (1 : ℤ) N r
  simp only [one_pow, one_mul] at h
  rw [Finset.sum_const, card_filter_binaryWeight_eq, nsmul_eq_mul,
    mul_one] at h
  exact h.symm

end Fabius
