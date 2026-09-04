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

* The **general filter** `sum_filter_modEq_mul_natCast`, over any
  field and any coefficient function `f`,
  `q·∑_{n<N, n≡r (q)} f(n) = ∑_{ℓ<q} (ζ⁻¹)^(rℓ)·∑_{n<N} f(n)ζ^(nℓ)`,
  lives in `ThueMorseFourierInversion`, next to the character
  orthogonality it is built on; this module specializes it.
* `thueMorse_rarefied_filter` — the specialization
  `q·A_{m,r}^{(q)} = ∑_{ℓ<q} ζ_q^(-rℓ)·∏_{j<m}(1-ζ_q^(ℓ·2^j))`
  over `ℂ`, with the transform written as the finite product
  (`sum_thueMorseSign_pow_mul`).
* `sum_filter_mod_eq_sum_range` — the **residue-class reindexation**
  for an arbitrary modulus `b` and residue `r < b`, for an arbitrary
  function into an arbitrary additive commutative monoid:
  `∑_{n<N, n≡r (b)} f(n) = ∑_{k<(N-r+b-1)/b} f(bk+r)`.
* `sum_filter_even_eq_sum_range`, `sum_filter_odd_eq_sum_range` — the
  **halving reindexations**, its two instances at `b = 2`:
  `∑_{n<N, n even} f(n) = ∑_{k<(N+1)/2} f(2k)` and
  `∑_{n<N, n odd} f(n) = ∑_{k<N/2} f(2k+1)`.
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

/-! ### The rarefied filter over the complex roots of unity -/

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

/-! ### Reindexing a residue class: modulus `b`, then modulus two -/

/-- **Extracting a residue class from a range.**  For `r < b`, the map
`k ↦ b·k + r` is a bijection from `range ⌈(N-r)/b⌉ =
range ((N - r + b - 1)/b)` onto the elements of `range N` congruent to
`r` modulo `b`, so any sum over that residue class is a plain range
sum: `∑_{n<N, n ≡ r (b)} f(n) = ∑_{k<(N-r+b-1)/b} f(bk + r)`.  The
index count is `⌈(N - r)/b⌉` when `r < N` and `0` when `N ≤ r`
(truncated subtraction).  Stated for an arbitrary function into an
arbitrary additive commutative monoid; the two halving lemmas below
are its instances at `b = 2`. -/
theorem sum_filter_mod_eq_sum_range {M : Type*} [AddCommMonoid M]
    (b r : ℕ) (hr : r < b) (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % b = r), f n =
      ∑ k ∈ range ((N - r + b - 1) / b), f (b * k + r) := by
  have hb : 0 < b := by omega
  have himg : (range N).filter (fun n => n % b = r) =
      (range ((N - r + b - 1) / b)).image (fun k => b * k + r) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, hmod⟩
      have hdm : b * (n / b) + r = n := by
        rw [← hmod]
        exact Nat.div_add_mod n b
      refine ⟨n / b, ?_, hdm⟩
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hb, add_mul,
        one_mul, Nat.mul_comm (n / b) b]
      omega
    · rintro ⟨k, hk, rfl⟩
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hb, add_mul,
        one_mul, Nat.mul_comm k b] at hk
      exact ⟨by omega, by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]⟩
  rw [himg]
  exact Finset.sum_image fun a₁ _ a₂ _ h =>
    Nat.eq_of_mul_eq_mul_left hb (by omega)

/-- **Halving the even part of a range.**  The map `k ↦ 2k` is a
bijection from `range ⌈N/2⌉ = range ((N+1)/2)` onto the even elements of
`range N`, so any sum over the even indices below `N` is a plain range
sum of the doubled function:
`∑_{n<N, n even} f(n) = ∑_{k<(N+1)/2} f(2k)`.  Stated for an arbitrary
function into an arbitrary additive commutative monoid; the instance
`b = 2`, `r = 0` of `sum_filter_mod_eq_sum_range`. -/
theorem sum_filter_even_eq_sum_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % 2 = 0), f n =
      ∑ k ∈ range ((N + 1) / 2), f (2 * k) := by
  have h := sum_filter_mod_eq_sum_range 2 0 (by omega) f N
  rw [show (N - 0 + 2 - 1) / 2 = (N + 1) / 2 by omega] at h
  simp only [add_zero] at h
  exact h

/-- **Halving the odd part of a range.**  The map `k ↦ 2k+1` is a
bijection from `range ⌊N/2⌋` onto the odd elements of `range N`:
`∑_{n<N, n odd} f(n) = ∑_{k<N/2} f(2k+1)`.  Companion of
`sum_filter_even_eq_sum_range`, over an arbitrary additive commutative
monoid; the instance `b = 2`, `r = 1` of
`sum_filter_mod_eq_sum_range`. -/
theorem sum_filter_odd_eq_sum_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => n % 2 = 1), f n =
      ∑ k ∈ range (N / 2), f (2 * k + 1) := by
  have h := sum_filter_mod_eq_sum_range 2 1 (by omega) f N
  rw [show (N - 1 + 2 - 1) / 2 = N / 2 by omega] at h
  exact h

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

/-- The `mod 4` bookkeeping shared by the two closed forms below.  A
prefix sum in residue form, `if P % 2 = 0 then 0 else ε(P/2)`, equals
`if C then ε(N/4) else 0` as soon as the parity of `P` decides `C` and
`P/2 = N/4` whenever `P` is odd. -/
private theorem ite_mod_two_eq_ite (N P : ℕ) (C : Prop) [Decidable C]
    (hC : P % 2 = 0 ↔ ¬ C) (hdiv : P % 2 ≠ 0 → P / 2 = N / 4) :
    (if P % 2 = 0 then (0 : ℤ) else thueMorseSign (P / 2)) =
      if C then thueMorseSign (N / 4) else 0 := by
  by_cases h : P % 2 = 0
  · rw [if_pos h, if_neg (hC.mp h)]
  · rw [if_neg h, if_pos (not_not.mp fun hc => h (hC.mpr hc)), hdiv h]

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
  exact ite_mod_two_eq_ite N ((N + 1) / 2) (N % 4 = 1 ∨ N % 4 = 2)
    ⟨fun h => by omega, fun h => by omega⟩ (fun h => by omega)

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
    sum_thueMorseSign_range_mod_two,
    ite_mod_two_eq_ite N (N / 2) (N % 4 = 2 ∨ N % 4 = 3)
      ⟨fun h => by omega, fun h => by omega⟩ (fun _ => by omega),
    apply_ite Neg.neg, neg_zero]

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
