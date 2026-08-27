import FabiusFunction.ThueMorseFourierInversion
import FabiusFunction.ThueMorseEulerTransform

/-!
# The root-of-unity filter for rarefied Thue–Morse sums

Averaging characters over a full period extracts an arithmetic
progression: `(1/q)·∑_{ℓ<q} ζ^((n-r)ℓ) = [n ≡ r (mod q)]` for a
primitive `q`-th root of unity `ζ`.  Applied to the Thue–Morse block
polynomial this yields the atlas's exact finite formula for the
rarefied partial sums — the entry point to Newman's phenomenon.

For the smallest modulus `q = 2` no roots of unity are needed at all:
halving the index carries the even (resp. odd) part of `range N` onto a
plain prefix range, and the closed form of the signed prefix sums then
evaluates both filtered sums for **every** `N` — the answer depends only
on `N mod 4` and on the single sign `ε(⌊N/4⌋)`.

* `sum_filter_modEq_mul_natCast` — the **general filter**, over any
  field and any coefficient function `f`:
  `q·∑_{n<N, n≡r (q)} f(n) = ∑_{ℓ<q} (ζ⁻¹)^(rℓ)·∑_{n<N} f(n)ζ^(nℓ)`.
* `thueMorse_rarefied_filter` — the specialization
  `q·A_{m,r}^{(q)} = ∑_{ℓ<q} ζ_q^(-rℓ)·∏_{j<m}(1-ζ_q^(ℓ·2^j))`
  over `ℂ`, with the transform written as the finite product
  (`sum_thueMorseSign_pow_mul`).
* `sum_filter_even_eq_sum_range`, `sum_filter_odd_eq_sum_range` — the
  **halving reindexations**, for an arbitrary function into an arbitrary
  additive commutative monoid: `∑_{n<N, n even} f(n) = ∑_{k<(N+1)/2}
  f(2k)` and `∑_{n<N, n odd} f(n) = ∑_{k<N/2} f(2k+1)`.
* `sum_thueMorseSign_range_mod_two` — the signed prefix sum in residue
  form: `∑_{t<N} ε(t)` is `0` for even `N` and `ε(N/2)` for odd `N`.
* `sum_thueMorseSign_filter_even_eq_sum_range` and
  `sum_thueMorseSign_filter_odd_eq_sum_range` — the two halves of a
  range, expressed as prefix sums: `∑_{n<N, n even} ε(n) =
  ∑_{k<(N+1)/2} ε(k)` and `∑_{n<N, n odd} ε(n) = -∑_{k<N/2} ε(k)`.
* `sum_thueMorseSign_filter_even` and `sum_thueMorseSign_filter_odd` —
  the **`q = 2` filter in closed form, for every `N`**:
  `∑_{n<N, n even} ε(n)` equals `ε(⌊N/4⌋)` when `N ≡ 1, 2 (mod 4)` and
  `0` otherwise, while `∑_{n<N, n odd} ε(n)` equals `-ε(⌊N/4⌋)` when
  `N ≡ 2, 3 (mod 4)` and `0` otherwise.
* `abs_sum_thueMorseSign_filter_even_le_one` and
  `abs_sum_thueMorseSign_filter_odd_le_one` — consequently each filtered
  partial sum is `0` or `±1`, uniformly in `N`.
* `sum_thueMorseSign_even_range` — the even-modulus collapse
  `A_{m,0}^{(2)} = 0` for `m ≥ 2`, now a corollary of the closed form:
  `2^m ≡ 0 (mod 4)` lands in the vanishing branch.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The general root-of-unity filter -/

/-- **The root-of-unity filter**, in full generality: for a primitive
`q`-th root of unity `ζ` in a field and any `f`, the progression
`n ≡ r (mod q)` is extracted from `range N` by averaging twisted
transforms:
`q·∑_{n<N, n≡r} f(n) = ∑_{ℓ<q} (ζ⁻¹)^(rℓ)·∑_{n<N} f(n)ζ^(nℓ)`. -/
theorem sum_filter_modEq_mul_natCast {F : Type*} [Field F] [DecidableEq F]
    {ζ : F} {q : ℕ} (hζ : IsPrimitiveRoot ζ q) (hq : q ≠ 0)
    (f : ℕ → F) (N r : ℕ) :
    (q : F) * ∑ n ∈ (range N).filter (fun n => n % q = r % q), f n =
      ∑ ℓ ∈ range q, (ζ⁻¹) ^ (r * ℓ) * ∑ n ∈ range N, f n * ζ ^ (n * ℓ) := by
  symm
  have hstep : ∀ ℓ ∈ range q,
      (ζ⁻¹) ^ (r * ℓ) * ∑ n ∈ range N, f n * ζ ^ (n * ℓ) =
      ∑ n ∈ range N, f n * (ζ ^ n * (ζ⁻¹) ^ r) ^ ℓ := by
    intro ℓ _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hsplit : (ζ ^ n * (ζ⁻¹) ^ r) ^ ℓ =
        ζ ^ (n * ℓ) * (ζ⁻¹) ^ (r * ℓ) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [hsplit]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hinner : ∀ n ∈ range N,
      ∑ ℓ ∈ range q, f n * (ζ ^ n * (ζ⁻¹) ^ r) ^ ℓ =
      f n * (if n % q = r % q then (q : F) else 0) := by
    intro n _
    rw [← Finset.mul_sum, sum_pow_mul_inv_pow_eq_ite hζ hq n r]
  rw [Finset.sum_congr rfl hinner, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

/-- **The rarefied filter formula** (the atlas's boxed identity): with
`ζ_q = e^(2πi/q)`,
`q·A_{m,r}^{(q)} = ∑_{ℓ<q} ζ_q^(-rℓ)·∏_{j<m}(1 - ζ_q^(ℓ·2^j))` —
each twisted transform of the Thue–Morse block collapses to the finite
product, which is exactly `sum_thueMorseSign_pow_mul`. -/
theorem thueMorse_rarefied_filter (q : ℕ) (hq : q ≠ 0) (m r : ℕ) :
    (q : ℂ) * ∑ n ∈ (range (2 ^ m)).filter (fun n => n % q = r % q),
        ((thueMorseSign n : ℤ) : ℂ) =
      ∑ ℓ ∈ range q,
        ((Complex.exp (2 * Real.pi * Complex.I / q))⁻¹) ^ (r * ℓ) *
          ∏ j ∈ range m,
            (1 - Complex.exp (2 * Real.pi * Complex.I / q) ^ (ℓ * 2 ^ j)) := by
  have hprim : IsPrimitiveRoot
      (Complex.exp (2 * Real.pi * Complex.I / q)) q :=
    Complex.isPrimitiveRoot_exp q hq
  rw [sum_filter_modEq_mul_natCast hprim hq]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [sum_thueMorseSign_pow_mul
    (Complex.exp (2 * Real.pi * Complex.I / q)) m ℓ]

/-! ### Halving a range: the modulus-two reindexations -/

/-- **Halving the even part of a range.**  The map `k ↦ 2k` is a
bijection from `range ⌈N/2⌉ = range ((N+1)/2)` onto the even elements of
`range N`, so any sum over the even indices below `N` is a plain range
sum of the doubled function:
`∑_{n<N, n even} f(n) = ∑_{k<(N+1)/2} f(2k)`.  Stated for an arbitrary
function into an arbitrary additive commutative monoid. -/
theorem sum_filter_even_eq_sum_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % 2 = 0), f n =
      ∑ k ∈ range ((N + 1) / 2), f (2 * k) := by
  have himg : (range N).filter (fun n => n % 2 = 0) =
      (range ((N + 1) / 2)).image (fun k => 2 * k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, hpar⟩
      exact ⟨n / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [himg]
  exact Finset.sum_image (fun a _ b _ h => by omega)

/-- **Halving the odd part of a range.**  The map `k ↦ 2k+1` is a
bijection from `range ⌊N/2⌋` onto the odd elements of `range N`:
`∑_{n<N, n odd} f(n) = ∑_{k<N/2} f(2k+1)`.  Companion of
`sum_filter_even_eq_sum_range`, over an arbitrary additive commutative
monoid. -/
theorem sum_filter_odd_eq_sum_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % 2 = 1), f n =
      ∑ k ∈ range (N / 2), f (2 * k + 1) := by
  have himg : (range N).filter (fun n => n % 2 = 1) =
      (range (N / 2)).image (fun k => 2 * k + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, hpar⟩
      exact ⟨n / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [himg]
  exact Finset.sum_image (fun a _ b _ h => by omega)

/-! ### The modulus-two filter in closed form -/

/-- `sum_thueMorseSign_range` in residue form: `∑_{t<N} ε(t)` is `0` when
`N` is even and `ε(N/2)` when `N` is odd.  Only the phrasing of the test
changes — `N % 2 = 0` in place of `2 ∣ N` — which is the shape the
`mod 4` case analysis below runs on. -/
theorem sum_thueMorseSign_range_mod_two (N : ℕ) :
    ∑ t ∈ range N, thueMorseSign t =
      if N % 2 = 0 then 0 else thueMorseSign (N / 2) := by
  rw [sum_thueMorseSign_range]
  rcases Nat.even_or_odd N with ⟨M, rfl⟩ | ⟨M, rfl⟩
  · rw [if_pos (by omega : 2 ∣ M + M),
      if_pos (by omega : (M + M) % 2 = 0)]
  · rw [if_neg (by omega : ¬ (2 ∣ 2 * M + 1)),
      if_neg (by omega : ¬ ((2 * M + 1) % 2 = 0))]

/-- The even half of a signed prefix sum **is** a shorter signed prefix
sum: `∑_{n<N, n even} ε(n) = ∑_{k<(N+1)/2} ε(k)`, because `ε(2k) = ε(k)`.
-/
theorem sum_thueMorseSign_filter_even_eq_sum_range (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % 2 = 0), thueMorseSign n =
      ∑ k ∈ range ((N + 1) / 2), thueMorseSign k := by
  rw [sum_filter_even_eq_sum_range]
  exact Finset.sum_congr rfl fun k _ => thueMorseSign_two_mul k

/-- The odd half of a signed prefix sum is the *negative* of a shorter
signed prefix sum: `∑_{n<N, n odd} ε(n) = -∑_{k<N/2} ε(k)`, because
`ε(2k+1) = -ε(k)`. -/
theorem sum_thueMorseSign_filter_odd_eq_sum_range (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % 2 = 1), thueMorseSign n =
      -∑ k ∈ range (N / 2), thueMorseSign k := by
  have hodd : ∀ k ∈ range (N / 2),
      thueMorseSign (2 * k + 1) = -thueMorseSign k := fun k _ =>
    thueMorseSign_two_mul_add_one k
  rw [sum_filter_odd_eq_sum_range, Finset.sum_congr rfl hodd,
    Finset.sum_neg_distrib]

/-- **The even arithmetic filter, in closed form, for every `N`.**
`∑_{n<N, n even} ε(n) = ε(⌊N/4⌋)` when `N ≡ 1` or `2 (mod 4)`, and `0`
when `N ≡ 0` or `3 (mod 4)`.

Halving turns the sum into `∑_{k<(N+1)/2} ε(k)`, which vanishes exactly
when `(N+1)/2` is even — i.e. when `N ≡ 0, 3 (mod 4)` — and otherwise
equals `ε((N+1)/4) = ε(N/4)`.  Note that the *value* is `ε(⌊N/4⌋)`, one
Thue–Morse sign, so the filtered sums never exceed `1` in modulus. -/
theorem sum_thueMorseSign_filter_even (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % 2 = 0), thueMorseSign n =
      if N % 4 = 1 ∨ N % 4 = 2 then thueMorseSign (N / 4) else 0 := by
  rw [sum_thueMorseSign_filter_even_eq_sum_range,
    sum_thueMorseSign_range_mod_two]
  have h4 : N % 4 = 0 ∨ N % 4 = 1 ∨ N % 4 = 2 ∨ N % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · rw [if_pos (by omega : (N + 1) / 2 % 2 = 0),
      if_neg (by omega : ¬ (N % 4 = 1 ∨ N % 4 = 2))]
  · rw [if_neg (by omega : ¬ ((N + 1) / 2 % 2 = 0)),
      if_pos (by omega : N % 4 = 1 ∨ N % 4 = 2),
      show (N + 1) / 2 / 2 = N / 4 by omega]
  · rw [if_neg (by omega : ¬ ((N + 1) / 2 % 2 = 0)),
      if_pos (by omega : N % 4 = 1 ∨ N % 4 = 2),
      show (N + 1) / 2 / 2 = N / 4 by omega]
  · rw [if_pos (by omega : (N + 1) / 2 % 2 = 0),
      if_neg (by omega : ¬ (N % 4 = 1 ∨ N % 4 = 2))]

/-- **The odd arithmetic filter, in closed form, for every `N`.**
`∑_{n<N, n odd} ε(n) = -ε(⌊N/4⌋)` when `N ≡ 2` or `3 (mod 4)`, and `0`
when `N ≡ 0` or `1 (mod 4)`.

Together with `sum_thueMorseSign_filter_even` this recovers the full
prefix sum `sum_thueMorseSign_range`: the two closed forms cancel exactly
when `N ≡ 2 (mod 4)`, and for `N ≡ 1` (resp. `N ≡ 3`) one of them is zero
while the other carries the whole prefix sum. -/
theorem sum_thueMorseSign_filter_odd (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % 2 = 1), thueMorseSign n =
      if N % 4 = 2 ∨ N % 4 = 3 then -thueMorseSign (N / 4) else 0 := by
  rw [sum_thueMorseSign_filter_odd_eq_sum_range,
    sum_thueMorseSign_range_mod_two]
  have h4 : N % 4 = 0 ∨ N % 4 = 1 ∨ N % 4 = 2 ∨ N % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · rw [if_pos (by omega : N / 2 % 2 = 0),
      if_neg (by omega : ¬ (N % 4 = 2 ∨ N % 4 = 3)), neg_zero]
  · rw [if_pos (by omega : N / 2 % 2 = 0),
      if_neg (by omega : ¬ (N % 4 = 2 ∨ N % 4 = 3)), neg_zero]
  · rw [if_neg (by omega : ¬ (N / 2 % 2 = 0)),
      if_pos (by omega : N % 4 = 2 ∨ N % 4 = 3),
      show N / 2 / 2 = N / 4 by omega]
  · rw [if_neg (by omega : ¬ (N / 2 % 2 = 0)),
      if_pos (by omega : N % 4 = 2 ∨ N % 4 = 3),
      show N / 2 / 2 = N / 4 by omega]

/-- **The even-filtered discrepancy is at most one**: `|∑_{n<N, n even}
ε(n)| ≤ 1` for every `N`, since the closed form is a single sign or
zero. -/
theorem abs_sum_thueMorseSign_filter_even_le_one (N : ℕ) :
    |∑ n ∈ (range N).filter (fun n => n % 2 = 0), thueMorseSign n| ≤ 1 := by
  rw [sum_thueMorseSign_filter_even]
  split_ifs
  · rw [abs_thueMorseSign]
  · simp

/-- **The odd-filtered discrepancy is at most one**: `|∑_{n<N, n odd}
ε(n)| ≤ 1` for every `N`. -/
theorem abs_sum_thueMorseSign_filter_odd_le_one (N : ℕ) :
    |∑ n ∈ (range N).filter (fun n => n % 2 = 1), thueMorseSign n| ≤ 1 := by
  rw [sum_thueMorseSign_filter_odd]
  split_ifs
  · rw [abs_neg, abs_thueMorseSign]
  · simp

/-- **Even-modulus collapse**: the even rarefied sum vanishes,
`A_{m,0}^{(2)} = ∑_{n<2^m, n even} ε(n) = 0` for `m ≥ 2`.  A corollary of
`sum_thueMorseSign_filter_even`: `2^m` is divisible by `4`, hence lands
in the vanishing branch `N ≡ 0 (mod 4)`. -/
theorem sum_thueMorseSign_even_range (m : ℕ) (hm : 2 ≤ m) :
    ∑ n ∈ (range (2 ^ m)).filter (fun n => n % 2 = 0),
        thueMorseSign n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  have hfac : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by
    rw [pow_add]
    ring
  rw [sum_thueMorseSign_filter_even,
    if_neg (by omega : ¬ (2 ^ (k + 2) % 4 = 1 ∨ 2 ^ (k + 2) % 4 = 2))]

end Fabius
